module

public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import StacksFrontier.AlgebraicGeometry.Limits.LimitPreservingFunctorOfPoints
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtale.StandardVCoveringLimits
public import StacksFrontier.AlgebraicGeometry.Topologies.Vtopology.Sheaves
public import StacksCore.Tactic.StacksAttribute

/-!
# Sheaves for the V topology from sheaves for the h topology

A presheaf of sets on schemes which satisfies the sheaf condition for every covering family
that is locally of finite presentation and a V covering, and which turns cofiltered inverse
limits of affine schemes into filtered colimits of sets, satisfies the sheaf condition for
every V covering.

## Main results

* `AlgebraicGeometry.exists_affineSystem_of_isStandardVCovering_singleton` presents a standard
  V covering of affine schemes as a cofiltered inverse limit of affine schemes whose structure
  morphisms are locally of finite presentation and are V coverings.
* `AlgebraicGeometry.isVSheaf_of_isSheafFor_vCovering_of_isLimitPreserving` is the sheaf
  criterion itself.

## Implementation notes

Stacks 0ETS defines an h covering to be a family of morphisms locally of finite presentation
satisfying one of the two equivalent conditions of Stacks 0ETR -- being a ph covering, or
being a V covering.  The two readings are identified only by 0ETR, which sits far below this
file in the import graph — it rests on the Raynaud-Gruson flattening theorem — so a
formalization here has to choose one.  `AlgebraicGeometry.IsHCovering` fixes the ph reading;
the hypothesis here is the V reading, which is what the argument for 0EVQ actually consumes and
which therefore needs no appeal to 0ETR at all.  Since a ph covering is a V covering,
`AlgebraicGeometry.isVCovering_of_isPHCovering`, the hypothesis below is implied by the
h-covering sheaf condition in the ph reading through 0ETR, which this development proves as
`AlgebraicGeometry.isPHCovering_iff_isVCovering` in
`StacksFrontier/AlgebraicGeometry/Topologies/V/PhVFlatteningModification.lean`.

The V sheaf condition is reduced to the Zariski sheaf condition together with the sheaf
condition for a single morphism of affine schemes which is a standard V covering, by
`AlgebraicGeometry.isVSheaf_iff_zariski_and_standard` and
`AlgebraicGeometry.isStandardVSheaf_iff_singleton`.  An open covering is a V covering by
morphisms locally of finite presentation, so the Zariski condition is immediate.

For a single morphism `f : X ⟶ Y` of affine schemes which is a standard V covering, the source
is presented as `X = lim D i` with each `D i` affine over `Y` of finite presentation; this is
the hard implication of Stacks 0EVP, carried out here in the V reading, where it needs no
input beyond the colimit presentation of a ring as a directed system of finitely presented
algebras and the limit criterion for standard V coverings, Stacks 0EVN.  Limit preservation is
then applied twice, to that system and to the system of relative squares `i ↦ D i ×_Y D i`
whose limit is `X ×_Y X`; together the two applications say that filtered colimits of sets
commute with equalizers.

The index category of the presentation is produced at the size of the schemes, so limit
preservation is needed only for index categories of that size.  The system of relative squares
has a constant base, so its limit cone is built from the universal property of the original
limit applied to the two projections rather than by an interchange of limits, which is
unavailable at this size.

## References

* [Stacks Project, Tag 0EVQ](https://stacks.math.columbia.edu/tag/0EVQ)
* [Stacks Project, Tag 0EVP](https://stacks.math.columbia.edu/tag/0EVP)
* [Stacks Project, Tag 0ETM](https://stacks.math.columbia.edu/tag/0ETM)
* [Stacks Project, Tag 05LX](https://stacks.math.columbia.edu/tag/05LX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry

open AlgebraicGeometry.DirectedPresentation

/-- `Spec` turns a composite of ring maps, checked pointwise, into a composite of morphisms. -/
private theorem spec_map_comp_of_forall_eq {R S T : CommRingCat.{u}} (a : R ⟶ S) (b : S ⟶ T)
    (c : R ⟶ T) (h : ∀ x, b (a x) = c x) : Spec.map b ≫ Spec.map a = Spec.map c := by
  rw [← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext h))

/-- A morphism of affine schemes which is a standard V covering is a cofiltered inverse limit,
over its target, of affine schemes whose structure morphisms are locally of finite
presentation and are themselves V coverings. -/
theorem exists_affineSystem_of_isStandardVCovering_singleton
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (hStd : IsStandardVCovering (fun _ : Unit ↦ X) (fun _ ↦ f)) :
    ∃ (J : Type u) (_ : Category.{u} J) (_ : IsCofiltered J) (D : J ⥤ Scheme.{u})
      (t : D ⟶ (Functor.const J).obj Y) (p : (Functor.const J).obj X ⟶ D)
      (_ : IsLimit (Cone.mk X p)),
      (∀ i, IsAffine (D.obj i)) ∧ p ≫ t = (Functor.const J).map f ∧
        (∀ i, LocallyOfFinitePresentation (t.app i)) ∧
        ∀ i, IsVCovering (fun _ : Unit ↦ D.obj i) (fun _ ↦ t.app i) := by
  let R : Type u := (Γ(Y, ⊤)).carrier
  let A : Type u := (Γ(X, ⊤)).carrier
  let : Algebra R A := f.appTop.hom.toAlgebra
  obtain ⟨Λ, hPO, hNonempty, hDirected, G, hComm, hAlg, q, hDS, g, hg, hFP, _, hbij⟩ :=
    Algebra.exists_directedSystem_finitePresentation_lift_bijective R A
  let : PartialOrder Λ := hPO
  let : Nonempty Λ := hNonempty
  let : IsDirectedOrder Λ := hDirected
  let : ∀ i, CommRing (G i) := hComm
  let : ∀ i, Algebra R (G i) := hAlg
  let : DirectedSystem G (fun i j h ↦ ⇑(q i j h)) := hDS
  let Fd : Λ ⥤ CommRingCat.{u} := ringDiagram G q
  let C : Cocone Fd := compatibleCocone G q g hg
  have hC : IsColimit C := compatibleIsColimit G q g hg hbij
  let D : Λᵒᵖ ⥤ Scheme.{u} := Fd.op ⋙ Scheme.Spec
  let c₀ : Cone D := Scheme.Spec.mapCone (Cocone.op C)
  have hc₀ : IsLimit c₀ := isLimitOfPreserves Scheme.Spec hC.op
  have (i : Λᵒᵖ) : IsAffine (D.obj i) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (G i.unop))))
  have (i : Λᵒᵖ) : IsAffine (((Functor.const Λᵒᵖ).obj Y).obj i) := inferInstanceAs (IsAffine Y)
  let p : (Functor.const Λᵒᵖ).obj X ⟶ D :=
    { app i := by
        change X ⟶ Spec (CommRingCat.of (G i.unop))
        exact X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (g i.unop).toRingHom)
      naturality := by
        intro i j α
        have hij : j.unop ≤ i.unop := (α.unop).le
        change X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (g j.unop).toRingHom) =
          (X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (g i.unop).toRingHom)) ≫
            Spec.map (CommRingCat.ofHom (q j.unop i.unop hij).toRingHom)
        rw [Category.assoc, spec_map_comp_of_forall_eq
          (CommRingCat.ofHom (q j.unop i.unop hij).toRingHom)
          (CommRingCat.ofHom (g i.unop).toRingHom) (CommRingCat.ofHom (g j.unop).toRingHom)
          (hg j.unop i.unop hij)] }
  let cX : Cone D := Cone.mk X p
  have hcX : IsLimit cX := by
    let eX : c₀.pt ≅ X := by
      change Spec (CommRingCat.of A) ≅ X
      exact X.isoSpec.symm
    apply hc₀.ofIsoLimit (Cone.ext (c := c₀) (c' := cX) eX (by
      intro i
      dsimp [cX, p, c₀, D, Fd, C, compatibleCocone, ringDiagram, eX]
      rw [Iso.inv_hom_id_assoc]))
  let t : D ⟶ (Functor.const Λᵒᵖ).obj Y :=
    { app i := by
        change Spec (CommRingCat.of (G i.unop)) ⟶ Y
        exact Spec.map (CommRingCat.ofHom (algebraMap R (G i.unop))) ≫ Y.isoSpec.inv
      naturality := by
        intro i j α
        have hij : j.unop ≤ i.unop := (α.unop).le
        change Spec.map (CommRingCat.ofHom (q j.unop i.unop hij).toRingHom) ≫
            (Spec.map (CommRingCat.ofHom (algebraMap R (G j.unop))) ≫ Y.isoSpec.inv) =
          (Spec.map (CommRingCat.ofHom (algebraMap R (G i.unop))) ≫ Y.isoSpec.inv) ≫ 𝟙 Y
        rw [← Category.assoc, spec_map_comp_of_forall_eq
          (CommRingCat.ofHom (algebraMap R (G j.unop)))
          (CommRingCat.ofHom (q j.unop i.unop hij).toRingHom)
          (CommRingCat.ofHom (algebraMap R (G i.unop)))
          ((q j.unop i.unop hij).commutes)]
        simp }
  have hcompat : p ≫ t = (Functor.const Λᵒᵖ).map f := by
    ext i
    dsimp [p, t]
    change X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (g i.unop).toRingHom) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap R (G i.unop))) ≫ Y.isoSpec.inv) = f
    have hbase := spec_map_comp_of_forall_eq (CommRingCat.ofHom (algebraMap R (G i.unop)))
      (CommRingCat.ofHom (g i.unop).toRingHom) (CommRingCat.ofHom f.appTop.hom) fun x ↦
        ((g i.unop).commutes x).trans (by simp [A, RingHom.algebraMap_toAlgebra])
    have hnat : X.isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom f.appTop.hom) = f ≫ Y.isoSpec.hom := by
      simpa using Scheme.isoSpec_hom_naturality f
    calc
      _ = (X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom f.appTop.hom)) ≫
          Y.isoSpec.inv := by rw [Category.assoc, reassoc_of% hbase]
      _ = f := by rw [hnat]; simp
  have hΓ : IsColimit ((Scheme.Γ ⋙ forget CommRingCat).mapCocone cX.op) := by
    have (i : (Λᵒᵖ)ᵒᵖ) : IsAffine (D.op.obj i).unop := by
      change IsAffine (D.obj i.unop)
      infer_instance
    exact isColimitOfPreserves (forget CommRingCat) (isColimitOfPreserves Scheme.Γ hcX.op)
  have hStage : ∀ i, IsStandardVCovering (fun _ : Unit ↦ D.obj i) (fun _ ↦ t.app i) :=
    (ProEtale.isStandardVCovering_limit_iff D t cX hcX hΓ f hcompat).mp hStd
  have hlfp : ∀ i, LocallyOfFinitePresentation (t.app i) := by
    intro i
    have hlfpSpec : LocallyOfFinitePresentation
        (Spec.map (CommRingCat.ofHom (algebraMap R (G i.unop)))) :=
      (LocallyOfFinitePresentation.SpecMap_iff
        (CommRingCat.ofHom (algebraMap R (G i.unop)))).2 (by
          change (algebraMap R (G i.unop)).FinitePresentation
          rw [RingHom.finitePresentation_algebraMap]
          exact hFP i.unop)
    change LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap R (G i.unop))) ≫ Y.isoSpec.inv)
    let : LocallyOfFinitePresentation
        (Spec.map (CommRingCat.ofHom (algebraMap R (G i.unop)))) := hlfpSpec
    infer_instance
  exact ⟨Λᵒᵖ, inferInstance, inferInstance, D, t, p, hcX, (fun i ↦ inferInstance), hcompat,
    hlfp, fun i ↦ isVCovering_of_standardVCovering_singleton (t.app i) (hStage i)⟩

section Squares

namespace RelativeSquares

variable {C : Type*} [Category C] [HasPullbacks C] {J : Type*} [Category J]
  {B : C} {D : J ⥤ C} (t : D ⟶ (Functor.const J).obj B)

/-- The transition morphism between relative squares induced by a morphism of the index
category. -/
@[reducible] noncomputable def squareMap {i j : J} (α : i ⟶ j) :
    pullback (t.app i) (t.app i) ⟶ pullback (t.app j) (t.app j) :=
  pullback.lift (pullback.fst (t.app i) (t.app i) ≫ D.map α)
    (pullback.snd (t.app i) (t.app i) ≫ D.map α) (by
      rw [Category.assoc, Category.assoc, show D.map α ≫ t.app j = t.app i by simp]
      exact pullback.condition)

/-- The transition morphism between relative squares commutes with the first projection. -/
@[reassoc (attr := simp)]
lemma squareMap_fst {i j : J} (α : i ⟶ j) :
    squareMap t α ≫ pullback.fst (t.app j) (t.app j) =
      pullback.fst (t.app i) (t.app i) ≫ D.map α :=
  pullback.lift_fst _ _ _

/-- The transition morphism between relative squares commutes with the second projection. -/
@[reassoc (attr := simp)]
lemma squareMap_snd {i j : J} (α : i ⟶ j) :
    squareMap t α ≫ pullback.snd (t.app j) (t.app j) =
      pullback.snd (t.app i) (t.app i) ≫ D.map α :=
  pullback.lift_snd _ _ _

/-- The inverse system of relative squares of a system over a fixed base: at `i` it is the
fibre product of the structure morphism at `i` with itself. -/
@[reducible] noncomputable def squareDiagram : J ⥤ C where
  obj i := pullback (t.app i) (t.app i)
  map α := squareMap t α
  map_id i := by apply pullback.hom_ext <;> simp
  map_comp α β := by apply pullback.hom_ext <;> simp

/-- The first projection from the system of relative squares. -/
@[reducible] noncomputable def squareFst : squareDiagram t ⟶ D where
  app i := pullback.fst (t.app i) (t.app i)
  naturality _ _ α := squareMap_fst t α

/-- The second projection from the system of relative squares. -/
@[reducible] noncomputable def squareSnd : squareDiagram t ⟶ D where
  app i := pullback.snd (t.app i) (t.app i)
  naturality _ _ α := squareMap_snd t α

/-- The morphism from the relative square of the limit morphism to the relative square at a
stage of the system. -/
@[reducible] noncomputable def squareLift (c : Cone D) (f : c.pt ⟶ B)
    (hf : ∀ i, c.π.app i ≫ t.app i = f) (i : J) :
    pullback f f ⟶ pullback (t.app i) (t.app i) :=
  pullback.lift (pullback.fst f f ≫ c.π.app i) (pullback.snd f f ≫ c.π.app i)
    (by rw [Category.assoc, Category.assoc, hf i]; exact pullback.condition)

/-- The morphism into a stage of the system of relative squares commutes with the first
projection. -/
@[reassoc (attr := simp)]
lemma squareLift_fst (c : Cone D) (f : c.pt ⟶ B)
    (hf : ∀ i, c.π.app i ≫ t.app i = f) (i : J) :
    squareLift t c f hf i ≫ pullback.fst (t.app i) (t.app i) =
      pullback.fst f f ≫ c.π.app i :=
  pullback.lift_fst _ _ _

/-- The morphism into a stage of the system of relative squares commutes with the second
projection. -/
@[reassoc (attr := simp)]
lemma squareLift_snd (c : Cone D) (f : c.pt ⟶ B)
    (hf : ∀ i, c.π.app i ≫ t.app i = f) (i : J) :
    squareLift t c f hf i ≫ pullback.snd (t.app i) (t.app i) =
      pullback.snd f f ≫ c.π.app i :=
  pullback.lift_snd _ _ _

/-- The relative square of the limit morphism, as a cone over the system of relative
squares. -/
@[reducible] noncomputable def squareCone (c : Cone D) (f : c.pt ⟶ B)
    (hf : ∀ i, c.π.app i ≫ t.app i = f) : Cone (squareDiagram t) where
  pt := pullback f f
  π :=
    { app := fun i => squareLift t c f hf i
      naturality := fun i j α => by
        have hnat : c.π.app i ≫ D.map α = c.π.app j := by simp
        apply pullback.hom_ext <;> simp [hnat] }

/-- The relative square of the limit morphism is the limit of the relative squares of the
stages. -/
noncomputable def isLimitSquareCone [Nonempty J] (c : Cone D) (f : c.pt ⟶ B)
    (hf : ∀ i, c.π.app i ≫ t.app i = f) (hc : IsLimit c) :
    IsLimit (squareCone t c f hf) := by
  let fstCone (s : Cone (squareDiagram t)) : Cone D :=
    (Cone.postcompose (squareFst t)).obj s
  let sndCone (s : Cone (squareDiagram t)) : Cone D :=
    (Cone.postcompose (squareSnd t)).obj s
  have hcomm (s : Cone (squareDiagram t)) :
      hc.lift (fstCone s) ≫ f = hc.lift (sndCone s) ≫ f := by
    obtain ⟨i⟩ := ‹Nonempty J›
    rw [← hf i, ← Category.assoc, ← Category.assoc, hc.fac, hc.fac]
    exact (Category.assoc _ _ _).trans
      ((congrArg (s.π.app i ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)
  refine ⟨fun s => pullback.lift (hc.lift (fstCone s)) (hc.lift (sndCone s)) (hcomm s), ?_, ?_⟩
  · intro s i
    apply pullback.hom_ext
    · rw [Category.assoc, squareLift_fst t c f hf, ← Category.assoc, pullback.lift_fst]
      exact hc.fac (fstCone s) i
    · rw [Category.assoc, squareLift_snd t c f hf, ← Category.assoc, pullback.lift_snd]
      exact hc.fac (sndCone s) i
  · intro s m hm
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      refine hc.uniq (fstCone s) _ fun i => ?_
      have hmi := congrArg (· ≫ pullback.fst (t.app i) (t.app i)) (hm i)
      rwa [Category.assoc, squareLift_fst t c f hf, ← Category.assoc] at hmi
    · rw [pullback.lift_snd]
      refine hc.uniq (sndCone s) _ fun i => ?_
      have hmi := congrArg (· ≫ pullback.snd (t.app i) (t.app i)) (hm i)
      rwa [Category.assoc, squareLift_snd t c f hf, ← Category.assoc] at hmi

end RelativeSquares

end Squares

section Equalizer

namespace RelativeSquares

variable {C : Type*} [Category C] [HasPullbacks C] {J : Type*} [Category J]
  {B : C} {D : J ⥤ C} (t : D ⟶ (Functor.const J).obj B)

omit [HasPullbacks C] in
/-- Functoriality of a presheaf, read on a composite of two morphisms. -/
lemma map_op_comp (F : Cᵒᵖ ⥤ Type*) {Z₁ Z₂ Z₃ : C} (a : Z₁ ⟶ Z₂) (b : Z₂ ⟶ Z₃)
    (x : F.obj (Opposite.op Z₃)) : F.map a.op (F.map b.op x) = F.map (a ≫ b).op x := by
  rw [op_comp, F.map_comp]
  rfl

/-- A presheaf which turns a cofiltered inverse limit of a system over a fixed base, and the
inverse limit of the relative squares of that system, into filtered colimits of sets satisfies
the one-arrow sheaf condition for the limit morphism as soon as it satisfies it for every
stage morphism. -/
lemma isSheafFor_singleton_of_isColimit [IsCofiltered J] (c : Cone D) (f : c.pt ⟶ B)
    (hf : ∀ i, c.π.app i ≫ t.app i = f) (F : Cᵒᵖ ⥤ Type*)
    (hcol : IsColimit (F.mapCocone c.op))
    (hsq : IsColimit (F.mapCocone (squareCone t c f hf).op))
    (hstage : ∀ i, Presieve.IsSheafFor F (Presieve.singleton (t.app i))) :
    Presieve.IsSheafFor F (Presieve.singleton f) := by
  have hinj : Function.Injective (F.map f.op) := by
    intro y z hyz
    obtain ⟨i⟩ := IsCofiltered.nonempty (C := J)
    have hfac : F.map (t.app i).op ≫ F.map (c.π.app i).op = F.map f.op := by
      rw [← F.map_comp, ← op_comp, hf]
    have heq : F.map (c.π.app i).op (F.map (t.app i).op y) =
        F.map (c.π.app i).op (F.map (t.app i).op z) := by
      change (F.map (t.app i).op ≫ F.map (c.π.app i).op) y =
        (F.map (t.app i).op ≫ F.map (c.π.app i).op) z
      rw [hfac]
      exact hyz
    obtain ⟨j, α, hα⟩ := (Types.FilteredColimit.isColimit_eq_iff' hcol _ _).mp heq
    have hstagej : Function.Injective (F.map (t.app j.unop).op) :=
      Presieve.isSeparatedFor_singleton.mp (hstage j.unop).isSeparatedFor
    have hnat : D.map α.unop ≫ t.app i = t.app j.unop := by simp
    have hfac' : F.map (t.app i).op ≫ F.map (D.map α.unop).op =
        F.map (t.app j.unop).op := by
      rw [← F.map_comp, ← op_comp, hnat]
    change (F.map (t.app i).op ≫ F.map (D.map α.unop).op) y =
      (F.map (t.app i).op ≫ F.map (D.map α.unop).op) z at hα
    rw [hfac'] at hα
    exact hstagej hα
  rw [Presieve.isSheafFor_singleton]
  intro x hx
  obtain ⟨i, xi, hxi⟩ := Types.jointly_surjective_of_isColimit hcol x
  change F.map (c.π.app i.unop).op xi = x at hxi
  have heq : F.map ((squareCone t c f hf).π.app i.unop).op
        (F.map (pullback.fst (t.app i.unop) (t.app i.unop)).op xi) =
      F.map ((squareCone t c f hf).π.app i.unop).op
        (F.map (pullback.snd (t.app i.unop) (t.app i.unop)).op xi) := by
    change F.map (squareLift t c f hf i.unop).op _ = F.map (squareLift t c f hf i.unop).op _
    rw [map_op_comp, map_op_comp, squareLift_fst, squareLift_snd, ← map_op_comp, ← map_op_comp,
      hxi]
    exact hx _ _ pullback.condition
  obtain ⟨j, α, hα⟩ := (Types.FilteredColimit.isColimit_eq_iff' hsq _ _).mp heq
  change F.map (squareMap t α.unop).op
      (F.map (pullback.fst (t.app i.unop) (t.app i.unop)).op xi) =
    F.map (squareMap t α.unop).op
      (F.map (pullback.snd (t.app i.unop) (t.app i.unop)).op xi) at hα
  rw [map_op_comp, map_op_comp, squareMap_fst, squareMap_snd] at hα
  have hcompat : F.map (pullback.fst (t.app j.unop) (t.app j.unop)).op
        (F.map (D.map α.unop).op xi) =
      F.map (pullback.snd (t.app j.unop) (t.app j.unop)).op
        (F.map (D.map α.unop).op xi) := by
    rwa [map_op_comp, map_op_comp]
  obtain ⟨y, hy, -⟩ := (Presieve.isSheafFor_singleton.mp (hstage j.unop))
    (F.map (D.map α.unop).op xi) (by
      intro Z q₁ q₂ hq
      have := congrArg (F.map (pullback.lift q₁ q₂ hq).op) hcompat
      simpa only [map_op_comp, ← Category.assoc, pullback.lift_fst, pullback.lift_snd] using this)
  have hone : F.map (c.π.app j.unop).op (F.map (t.app j.unop).op y) = F.map f.op y := by
    rw [map_op_comp, hf]
  have htwo : F.map (c.π.app j.unop).op (F.map (D.map α.unop).op xi) = x := by
    rwa [map_op_comp, show c.π.app j.unop ≫ D.map α.unop = c.π.app i.unop by simp]
  have hyx : F.map f.op y = x := by rw [← hone, hy, htwo]
  exact ⟨y, hyx, fun z hz => hinj (hz.trans hyx.symm)⟩

end RelativeSquares

end Equalizer

section Criterion

open RelativeSquares

/-- A constant family of arrows over a nonempty index type generates the presieve of the single
arrow it repeats. -/
lemma ofArrows_const_eq_singleton {C : Type*} [Category C] {T Z : C} (g : Z ⟶ T)
    (I : Type*) [Nonempty I] :
    Presieve.ofArrows (fun _ : I ↦ Z) (fun _ ↦ g) = Presieve.singleton g := by
  apply le_antisymm
  · exact Presieve.ofArrows_le_iff.mpr fun _ ↦ Presieve.singleton_self _
  · rw [Presieve.singleton_le_iff]
    exact ⟨Classical.arbitrary I⟩

/-- A singleton V covering stays a V covering after its index type is replaced by any nonempty
type. -/
lemma isVCovering_const_of_isVCovering {T Z : Scheme.{u}} (g : Z ⟶ T)
    (hg : IsVCovering (fun _ : Unit ↦ Z) (fun _ ↦ g)) (I : Type v) [Nonempty I] :
    IsVCovering (fun _ : I ↦ Z) (fun _ ↦ g) := by
  intro U hU
  obtain ⟨𝒰, hfin, haff, hstd, ⟨ρ⟩⟩ := hg U hU
  exact ⟨𝒰, hfin, haff, hstd,
    ⟨{ s₀ := fun _ ↦ Classical.arbitrary I, h₀ := ρ.h₀, w₀ := ρ.w₀ }⟩⟩

/-- A system of schemes over a fixed base, read as a system in the category of schemes over
that base. -/
@[reducible] private noncomputable def overDiagram {Y : Scheme.{u}} {J : Type*} [Category J]
    {D : J ⥤ Scheme.{u}} (t : D ⟶ (Functor.const J).obj Y) : J ⥤ Over Y where
  obj i := Over.mk (t.app i)
  map {i j} α := Over.homMk (D.map α) (by simp)
  map_id i := by
    apply Over.OverMorphism.ext
    simp
  map_comp α β := by
    apply Over.OverMorphism.ext
    simp

/-- A limit cone of a system of schemes over a fixed base, read as a cone in the category of
schemes over that base. -/
@[reducible] private noncomputable def overCone {Y : Scheme.{u}} {J : Type*} [Category J]
    {D : J ⥤ Scheme.{u}} (t : D ⟶ (Functor.const J).obj Y) (c : Cone D) (f : c.pt ⟶ Y)
    (hf : ∀ i, c.π.app i ≫ t.app i = f) : Cone (overDiagram t) where
  pt := Over.mk f
  π :=
    { app := fun i => Over.homMk (c.π.app i) (hf i)
      naturality := fun i j α => by
        apply Over.OverMorphism.ext
        simp }

/-- A cone over a nonempty system of schemes over a base is a limit cone as soon as its
underlying cone of schemes is one. -/
private noncomputable def isLimitOverCone {Y : Scheme.{u}} {J : Type*} [Category J]
    [Nonempty J] {D : J ⥤ Scheme.{u}} (t : D ⟶ (Functor.const J).obj Y) (c : Cone D)
    (f : c.pt ⟶ Y) (hf : ∀ i, c.π.app i ≫ t.app i = f) (hc : IsLimit c) :
    IsLimit (overCone t c f hf) := by
  refine ⟨fun s => Over.homMk (hc.lift ((Over.forget Y).mapCone s)) ?_, ?_, ?_⟩
  · obtain ⟨i⟩ := ‹Nonempty J›
    change hc.lift ((Over.forget Y).mapCone s) ≫ f = s.pt.hom
    rw [← hf i, ← Category.assoc]
    exact (congrArg (· ≫ t.app i) (hc.fac ((Over.forget Y).mapCone s) i)).trans (s.π.app i).w
  · exact fun s i ↦ Over.OverMorphism.ext (hc.fac _ i)
  · exact fun s m hm ↦ Over.OverMorphism.ext
      (hc.uniq ((Over.forget Y).mapCone s) m.left fun i ↦ congrArg (fun k ↦ k.left) (hm i))

/-- A limit preserving presheaf on schemes over `Y`, in the sense of Stacks 05LX, turns a
cofiltered inverse limit of affine schemes over `Y` into a filtered colimit of sets. -/
private noncomputable def isColimit_mapCocone_of_isLimitPreserving {Y : Scheme.{u}}
    (F : Scheme.{u}ᵒᵖ ⥤ Type w)
    (hLP : Scheme.IsLimitPreserving Y ((Over.forget Y).op ⋙ F))
    {J : Type u} [Category.{u} J] [IsCofiltered J] {D : J ⥤ Scheme.{u}}
    (t : D ⟶ (Functor.const J).obj Y) (c : Cone D) (hc : IsLimit c) (f : c.pt ⟶ Y)
    (hf : ∀ i, c.π.app i ≫ t.app i = f) (hD : ∀ i, IsAffine (D.obj i)) :
    IsColimit (F.mapCocone c.op) := by
  have : Nonempty J := IsCofiltered.nonempty
  exact Classical.choice
    ((hLP J (overDiagram t) hD).preserves (isLimitOverCone t c f hf hc).op)

/-- **Stacks 0EVQ.** A presheaf of sets on schemes which satisfies the sheaf condition for
every h covering and which is limit preserving in the sense of Stacks 05LX over every base
satisfies the sheaf condition for every V covering.

An h covering is a family of morphisms locally of finite presentation satisfying one of the
two equivalent conditions of Stacks 0ETR, and the condition used here is the second: being a V
covering. The equivalence with the first condition, being a ph covering, is Stacks 0ETR, which
rests on `AlgebraicGeometry.StandardVCoveringHasPHRefinement` and so on the Raynaud-Gruson
flattening theorem; with the first condition in place of the second the statement below would
have to carry that hypothesis, since the predicate cannot be named this far up the import
graph. -/
@[stacks 0EVQ]
theorem isVSheaf_of_isSheafFor_vCovering_of_isLimitPreserving (F : Scheme.{u}ᵒᵖ ⥤ Type w)
    (hH : ∀ (T : Scheme.{u}) (I : Type (max u v)) (X : I → Scheme.{u}) (g : ∀ i, X i ⟶ T),
      (∀ i, LocallyOfFinitePresentation (g i)) → IsVCovering X g →
        (Presieve.ofArrows X g).IsSheafFor F)
    (hLP : ∀ Y : Scheme.{u}, Scheme.IsLimitPreserving Y ((Over.forget Y).op ⋙ F)) :
    IsVSheaf.{u, max u v, w} F := by
  have hZar : ∀ (T : Scheme.{u}) (𝒰 : T.OpenCover.{max u v}),
      (Presieve.ofArrows 𝒰.X 𝒰.f).IsSheafFor F := fun T 𝒰 ↦
    hH T 𝒰.I₀ 𝒰.X 𝒰.f (fun _ ↦ inferInstance)
      (isVCovering_of_isPHCovering 𝒰.X 𝒰.f (IsPHCovering.of_openCover 𝒰))
  refine (isVSheaf_iff_zariski_and_standard.{u, v, w} F).mpr ⟨hZar, ?_⟩
  refine (isStandardVSheaf_iff_singleton.{u, v, w} F hZar).mpr ?_
  intro Y X hY hX f hstd
  obtain ⟨J, hJ, hJcof, D, t, p, hlim, haff, hcompat, hlfp, hV⟩ :=
    exists_affineSystem_of_isStandardVCovering_singleton f hstd
  let _ : Category.{u} J := hJ
  let _ : IsCofiltered J := hJcof
  have _ : Nonempty J := IsCofiltered.nonempty
  let _ : ∀ i, IsAffine (D.obj i) := haff
  have hfi : ∀ i, (Cone.mk X p).π.app i ≫ t.app i = f := fun i ↦ by
    simpa using NatTrans.congr_app hcompat i
  have hstage : ∀ i, (Presieve.singleton (t.app i)).IsSheafFor F := by
    intro i
    have h := hH Y (ULift.{max u v} Unit) (fun _ ↦ D.obj i) (fun _ ↦ t.app i)
      (fun _ ↦ hlfp i) (isVCovering_const_of_isVCovering (t.app i) (hV i) _)
    rwa [ofArrows_const_eq_singleton] at h
  have hsqaff : ∀ i, IsAffine (pullback (t.app i) (t.app i)) := by
    intro i
    have hYa : IsAffine (((Functor.const J).obj Y).obj i) := hY
    infer_instance
  have hsqf : ∀ i, (squareCone t (Cone.mk X p) f hfi).π.app i ≫ (squareFst t ≫ t).app i =
      pullback.fst f f ≫ f := by
    intro i
    calc (squareCone t (Cone.mk X p) f hfi).π.app i ≫ (squareFst t ≫ t).app i
        = (squareLift t (Cone.mk X p) f hfi i ≫
            pullback.fst (t.app i) (t.app i)) ≫ t.app i := (Category.assoc _ _ _).symm
      _ = (pullback.fst f f ≫ (Cone.mk X p).π.app i) ≫ t.app i := by
          rw [squareLift_fst t (Cone.mk X p) f hfi]
      _ = pullback.fst f f ≫ f := by rw [Category.assoc, hfi i]
  have hcol := isColimit_mapCocone_of_isLimitPreserving F (hLP Y) t (Cone.mk X p) hlim f hfi
    haff
  have hsq := isColimit_mapCocone_of_isLimitPreserving F (hLP Y) (squareFst t ≫ t)
    (squareCone t (Cone.mk X p) f hfi) (isLimitSquareCone t (Cone.mk X p) f hfi hlim)
    (pullback.fst f f ≫ f) hsqf hsqaff
  rw [ofArrows_const_eq_singleton f Unit]
  exact isSheafFor_singleton_of_isColimit t (Cone.mk X p) f hfi F hcol hsq hstage

end Criterion

end AlgebraicGeometry
