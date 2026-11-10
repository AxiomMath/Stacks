module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.SpecField
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.FiberedCategory.PairIsoClassPresheaf
public import StacksFrontier.Deformation.Artin.ChangeOfField.SiteRestriction
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.Artin.RimSchlessinger
public import StacksFrontier.Deformation.Artin.RimSchlessinger.Slice
public import StacksFrontier.Deformation.Artin.Versality
public import StacksFrontier.Deformation.ArtinCriteria.Predeformation
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.ResidueField.Basic
public import StacksFrontier.Deformation.ResidueField.Comparison
public import StacksFrontier.Deformation.Smooth.Basic

/-!
# Artinian charts over the stalk of the base

Given an Artinian local `Λ`-algebra `A` with residue field `l` and a point `s` of `S` below the
closed point of `Spec l`, this file makes `A` an algebra over the stalk `𝒪_{S,s}` compatibly with
its `Λ`-structure, and transports objects and morphisms of the deformation category over `Λ`
to the one over the stalk. Using these charts it deduces, from versality of an object at a
point `u`, the lifting property along surjections of Artinian local `Λ`-algebras with residue
field `κ(u)`, for any `Λ` whose base point is that of `u`.

These are ingredients of `Deformation.Artin.isSmooth_mapPredeformationCategory_of_isVersalAt`
(Stacks 07XG).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

-- `CategoryTheory.Functor.Fiber` is a plain `def`, so a term whose type mentions the underlying
-- object of a fibre -- such as the chosen cartesian lift `c.map f x`, whose source is
-- `(c.obj f x).1` where `(c.sliceFunctor x).obj f` is expected -- is not type-correct at
-- `implicit` transparency. Making it implicit-reducible here is what
-- `StacksFrontier.CategoryTheory.FiberedCategory.PairIsoClassPresheaf` does for the same reason.
attribute [local implicit_reducible]
  CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctor
  CategoryTheory.BasedFunctor.comp
  Deformation.changeOfFieldsBasedFunctor

universe u v w

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : Type v} [Category.{w} X] (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS)

variable (x : X)
variable {Λ l : Type u} [CommRing Λ] [Field l] [Algebra Λ l]
variable (iΛ : Spec (.of Λ) ⟶ S) (uₗ₀ : Over (p.obj x))
variable (huₗ₀ : (Over.forget (p.obj x) ⋙ Over.post B.inclusion).obj uₗ₀ =
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))

private theorem specMap_factors_through_named_stalk
    {A : Type u} [CommRing A] [IsLocalRing A]
    (f : Spec (.of A) ⟶ S) (s : S)
    (hs : f (IsLocalRing.closedPoint A) = s) :
    Spec.map ((S.presheaf.stalkCongr (.of_eq hs.symm)).hom ≫
      Scheme.stalkClosedPointTo f) ≫ S.fromSpecStalk s = f := by
  cases hs
  simpa using Scheme.Spec_stalkClosedPointTo_fromSpecStalk f

@[instance_reducible]
noncomputable def namedStalkAlgebraOfLocalSpecMap
    {A : Type u} [CommRing A] [IsLocalRing A]
    (f : Spec (.of A) ⟶ S) (s : S)
    (hs : f (IsLocalRing.closedPoint A) = s) :
    Algebra (S.presheaf.stalk s) A :=
  ((S.presheaf.stalkCongr (.of_eq hs.symm)).hom ≫
    Scheme.stalkClosedPointTo f).hom.toAlgebra

theorem chartArtin_closedPoint
    {Λ l A : Type u} [CommRing Λ] [Field l] [CommRing A] [IsLocalRing A]
    [Algebra Λ A] [Algebra Λ l]
    (r : A →+* l) (iΛ : Spec (.of Λ) ⟶ S) (g : Spec (.of l) ⟶ S)
    (hr : IsLocalHom r) (hres : r.comp (algebraMap Λ A) = algebraMap Λ l)
    (hpoint : Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ = g) :
    (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ)
      (IsLocalRing.closedPoint A) = g (IsLocalRing.closedPoint l) := by
  let : IsLocalHom r := hr
  have hclosed : Spec.map (CommRingCat.ofHom r) (IsLocalRing.closedPoint l) =
      IsLocalRing.closedPoint A := AlgebraicGeometry.Spec_closedPoint
        (f := CommRingCat.ofHom r)
  calc
    (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ)
        (IsLocalRing.closedPoint A) =
      (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ)
        (Spec.map (CommRingCat.ofHom r) (IsLocalRing.closedPoint l)) := by rw [hclosed]
    _ = (Spec.map (CommRingCat.ofHom (r.comp (algebraMap Λ A))) ≫ iΛ)
        (IsLocalRing.closedPoint l) := rfl
    _ = (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ)
        (IsLocalRing.closedPoint l) := by rw [hres]
    _ = g (IsLocalRing.closedPoint l) := by rw [hpoint]

theorem artinianResidueMap_comp_algebraMap
    {Λ l : Type u} [CommRing Λ] [Field l] [Algebra Λ l]
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ l) :
    (residueMap A).comp (algebraMap Λ A) = algebraMap Λ l := by
  ext a
  change A.residueEquiv (IsLocalRing.residue A (algebraMap Λ A a)) = algebraMap Λ l a
  calc
    A.residueEquiv (IsLocalRing.residue A (algebraMap Λ A a)) =
        A.residueEquiv (algebraMap Λ (IsLocalRing.ResidueField A) a) := by
          rw [← IsLocalRing.ResidueField.algebraMap_eq]
          exact congrArg A.residueEquiv
            (IsScalarTower.algebraMap_apply Λ A (IsLocalRing.ResidueField A) a).symm
    _ = algebraMap Λ l a := A.residueEquiv.commutes a

/-- The structure map `Spec A → S` of an Artinian chart sends the closed point to that of `g`. -/
private theorem chartArtin_closedPoint_artinian
    {Λ l : Type u} [CommRing Λ] [Field l] [Algebra Λ l]
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ l)
    (iΛ : Spec (.of Λ) ⟶ S) (g : Spec (.of l) ⟶ S)
    (hpoint : Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ = g) :
    (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ)
      (IsLocalRing.closedPoint A) = g (IsLocalRing.closedPoint l) := by
  let : IsLocalHom (A.residueEquiv.toRingEquiv) := inferInstance
  let : IsLocalHom (IsLocalRing.residue A) := inferInstance
  have hr : IsLocalHom (residueMap A) := by
    unfold residueMap
    infer_instance
  exact chartArtin_closedPoint S (residueMap A) iΛ g
    hr (artinianResidueMap_comp_algebraMap A) hpoint

/-- Ring maps out of a stalk are equal if their `Spec`s agree after `fromSpecStalk`. -/
private theorem stalk_hom_ext_of_comp_fromSpecStalk {s : S} {R : Type u} [CommRing R]
    {φ ψ : S.presheaf.stalk s →+* R}
    (h : Spec.map (CommRingCat.ofHom φ) ≫ S.fromSpecStalk s =
      Spec.map (CommRingCat.ofHom ψ) ≫ S.fromSpecStalk s) : φ = ψ :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono (S.fromSpecStalk s)).mp h))

@[instance_reducible]
noncomputable def chartArtinStalkAlgebra
    {Λ l : Type u} [CommRing Λ] [Field l] [Algebra Λ l]
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ l)
    (iΛ : Spec (.of Λ) ⟶ S) (g : Spec (.of l) ⟶ S) (s : S)
    (hs : g (IsLocalRing.closedPoint l) = s)
    (hpoint : Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ = g) :
    Algebra (S.presheaf.stalk s) A := by
  let f : Spec (.of A) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ
  letI : IsLocalHom (A.residueEquiv.toRingEquiv) := inferInstance
  letI : IsLocalHom (IsLocalRing.residue A) := inferInstance
  have hr : IsLocalHom (residueMap A) := by
    unfold residueMap
    infer_instance
  have hfa : f (IsLocalRing.closedPoint A) = g (IsLocalRing.closedPoint l) := by
    exact chartArtin_closedPoint S (residueMap A) iΛ g
      hr (artinianResidueMap_comp_algebraMap A) hpoint
  exact namedStalkAlgebraOfLocalSpecMap S f s (hfa.trans hs)

theorem chartArtin_base_eq_stalk
    {Λ l : Type u} [CommRing Λ] [Field l] [Algebra Λ l]
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ l)
    (iΛ : Spec (.of Λ) ⟶ S) (g : Spec (.of l) ⟶ S) (s : S)
    (hs : g (IsLocalRing.closedPoint l) = s)
    (hpoint : Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ = g) :
    letI := chartArtinStalkAlgebra S A iΛ g s hs hpoint
    Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) A)) ≫
      S.fromSpecStalk s =
        Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ := by
  let := chartArtinStalkAlgebra S A iΛ g s hs hpoint
  let f : Spec (.of A) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ
  exact specMap_factors_through_named_stalk S f s
    ((chartArtin_closedPoint_artinian S A iΛ g hpoint).trans hs)

theorem chartArtin_residueMap_comp_stalkAlgebraMap
    {Λ l : Type u} [CommRing Λ] [Field l] [Algebra Λ l]
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ l)
    (iΛ : Spec (.of Λ) ⟶ S) (g : Spec (.of l) ⟶ S) (s : S)
    (hs : g (IsLocalRing.closedPoint l) = s)
    [Algebra (S.presheaf.stalk s) l]
    (hRpoint : Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) l)) ≫
      S.fromSpecStalk s = g)
    (hpoint : Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ = g) :
    letI := chartArtinStalkAlgebra S A iΛ g s hs hpoint
    (residueMap A).comp (algebraMap (S.presheaf.stalk s) A) =
      algebraMap (S.presheaf.stalk s) l := by
  let := chartArtinStalkAlgebra S A iΛ g s hs hpoint
  let r := residueMap A
  let α := r.comp (algebraMap (S.presheaf.stalk s) A)
  have hcompα : Spec.map (CommRingCat.ofHom α) =
      Spec.map (CommRingCat.ofHom r) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) A)) := by
    dsimp [α]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hcompΛ : Spec.map (CommRingCat.ofHom (r.comp (algebraMap Λ A))) =
      Spec.map (CommRingCat.ofHom r) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Λ A)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hbase := chartArtin_base_eq_stalk S A iΛ g s hs hpoint
  have hleft : Spec.map (CommRingCat.ofHom α) ≫ S.fromSpecStalk s = g := by
    calc
      Spec.map (CommRingCat.ofHom α) ≫ S.fromSpecStalk s =
          Spec.map (CommRingCat.ofHom r) ≫
            (Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) A)) ≫
              S.fromSpecStalk s) := by
                rw [hcompα]
                simp [Category.assoc]
      _ = Spec.map (CommRingCat.ofHom r) ≫
            (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) :=
              congrArg (fun f => Spec.map (CommRingCat.ofHom r) ≫ f) hbase
      _ = Spec.map (CommRingCat.ofHom (r.comp (algebraMap Λ A))) ≫ iΛ := by
        rw [hcompΛ]
        simp [Category.assoc]
      _ = Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ := by
        rw [artinianResidueMap_comp_algebraMap A]
      _ = g := hpoint
  exact stalk_hom_ext_of_comp_fromSpecStalk S (hleft.trans hRpoint.symm)

noncomputable def chartArtinResidueEquiv
    {Λ l : Type u} [CommRing Λ] [Field l] [Algebra Λ l]
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ l)
    (iΛ : Spec (.of Λ) ⟶ S) (g : Spec (.of l) ⟶ S) (s : S)
    (hs : g (IsLocalRing.closedPoint l) = s)
    [Algebra (S.presheaf.stalk s) l]
    (hRpoint : Spec.map (CommRingCat.ofHom
      (algebraMap (S.presheaf.stalk s) l)) ≫ S.fromSpecStalk s = g)
    (hpoint : Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ = g) :
    letI := chartArtinStalkAlgebra S A iΛ g s hs hpoint
    IsLocalRing.ResidueField A ≃ₐ[S.presheaf.stalk s] l := by
  letI := chartArtinStalkAlgebra S A iΛ g s hs hpoint
  have hres := chartArtin_residueMap_comp_stalkAlgebraMap
    S A iΛ g s hs hRpoint hpoint
  refine { A.residueEquiv.toRingEquiv with commutes' := ?_ }
  intro r
  change A.residueEquiv (algebraMap (S.presheaf.stalk s)
    (IsLocalRing.ResidueField A) r) =
    algebraMap (S.presheaf.stalk s) l r
  calc
    A.residueEquiv (algebraMap (S.presheaf.stalk s)
      (IsLocalRing.ResidueField A) r) =
        A.residueEquiv (IsLocalRing.residue A
          (algebraMap (S.presheaf.stalk s) A r)) := by
            rw [IsScalarTower.algebraMap_apply (S.presheaf.stalk s) A
              (IsLocalRing.ResidueField A) r, ← IsLocalRing.ResidueField.algebraMap_eq]
    _ = residueMap A (algebraMap (S.presheaf.stalk s) A r) := rfl
    _ = algebraMap (S.presheaf.stalk s) l r :=
      congrArg (fun f : S.presheaf.stalk s →+* l => f r) hres

noncomputable def chartArtinObjectOverStalk
    {Λ l : Type u} [CommRing Λ] [Field l] [Algebra Λ l]
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ l)
    (iΛ : Spec (.of Λ) ⟶ S) (g : Spec (.of l) ⟶ S) (s : S)
    (hs : g (IsLocalRing.closedPoint l) = s)
    [Algebra (S.presheaf.stalk s) l]
    (hRpoint : Spec.map (CommRingCat.ofHom
      (algebraMap (S.presheaf.stalk s) l)) ≫ S.fromSpecStalk s = g)
    (hpoint : Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ = g) :
    Deformation.ArtinianLocalAlgCat.{u, u, u} (S.presheaf.stalk s) l := by
  letI : Algebra (S.presheaf.stalk s) A :=
    chartArtinStalkAlgebra S A iΛ g s hs hpoint
  exact
    { carrier := A
      commRing := inferInstance
      algebra := inferInstance
      isArtinianRing := inferInstance
      isLocalRing := inferInstance
      residueEquiv := chartArtinResidueEquiv S A iΛ g s hs hRpoint hpoint }

theorem chartArtinHom_stalkLinear
    {Λ l : Type u} [CommRing Λ] [Field l] [Algebra Λ l]
    (A B' : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ l)
    (f : A →ₐ[Λ] B') (iΛ : Spec (.of Λ) ⟶ S) (g : Spec (.of l) ⟶ S)
    (s : S) (hs : g (IsLocalRing.closedPoint l) = s)
    [Algebra (S.presheaf.stalk s) l]
    (hpoint : Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ = g) :
    letI := chartArtinStalkAlgebra S A iΛ g s hs hpoint
    letI := chartArtinStalkAlgebra S B' iΛ g s hs hpoint
    f.toRingHom.comp (algebraMap (S.presheaf.stalk s) A) =
      algebraMap (S.presheaf.stalk s) B' := by
  let := chartArtinStalkAlgebra S A iΛ g s hs hpoint
  let := chartArtinStalkAlgebra S B' iΛ g s hs hpoint
  let fA : Spec (.of A) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ
  let fB : Spec (.of B') ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap Λ B')) ≫ iΛ
  have hfactorA := chartArtin_base_eq_stalk S A iΛ g s hs hpoint
  have hfactorB := chartArtin_base_eq_stalk S B' iΛ g s hs hpoint
  have hcomp :
      Spec.map (CommRingCat.ofHom (f.toRingHom.comp
        (algebraMap (S.presheaf.stalk s) A))) =
        Spec.map (CommRingCat.ofHom f.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) A)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hcompΛ :
      Spec.map (CommRingCat.ofHom (f.toRingHom.comp (algebraMap Λ A))) =
        Spec.map (CommRingCat.ofHom f.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap Λ A)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hfΛ : f.toRingHom.comp (algebraMap Λ A) = algebraMap Λ B' := by
    ext a
    exact f.commutes a
  have hleft :
      Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) B')) ≫
        S.fromSpecStalk s = fB := hfactorB
  have hright :
      Spec.map (CommRingCat.ofHom (f.toRingHom.comp
        (algebraMap (S.presheaf.stalk s) A))) ≫ S.fromSpecStalk s = fB := by
    calc
      _ = Spec.map (CommRingCat.ofHom f.toRingHom) ≫
          (Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) A)) ≫
            S.fromSpecStalk s) := by
            rw [hcomp]
            simp [Category.assoc]
      _ = Spec.map (CommRingCat.ofHom f.toRingHom) ≫ fA := by
        exact congrArg (fun q => Spec.map (CommRingCat.ofHom f.toRingHom) ≫ q) hfactorA
      _ = fB := by
        calc
          Spec.map (CommRingCat.ofHom f.toRingHom) ≫ fA =
              Spec.map (CommRingCat.ofHom
                (f.toRingHom.comp (algebraMap Λ A))) ≫ iΛ := by
                  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
                    (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) = _
                  calc
                    _ = (Spec.map (CommRingCat.ofHom f.toRingHom) ≫
                        Spec.map (CommRingCat.ofHom (algebraMap Λ A))) ≫ iΛ := by
                          simp [Category.assoc]
                    _ = _ := congrArg (fun q => q ≫ iΛ) hcompΛ.symm
          _ = fB := by rw [hfΛ]
  exact (stalk_hom_ext_of_comp_fromSpecStalk S (hleft.trans hright.symm)).symm

noncomputable def chartArtinHomOverStalk
    {Λ l : Type u} [CommRing Λ] [Field l] [Algebra Λ l]
    (A B' : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ l)
    (f : A ⟶ B') (iΛ : Spec (.of Λ) ⟶ S) (g : Spec (.of l) ⟶ S) (s : S)
    (hs : g (IsLocalRing.closedPoint l) = s)
    [Algebra (S.presheaf.stalk s) l]
    (hRpoint : Spec.map (CommRingCat.ofHom
      (algebraMap (S.presheaf.stalk s) l)) ≫ S.fromSpecStalk s = g)
    (hpoint : Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ = g) :
    chartArtinObjectOverStalk S A iΛ g s hs hRpoint hpoint ⟶
      chartArtinObjectOverStalk S B' iΛ g s hs hRpoint hpoint := by
  letI := chartArtinStalkAlgebra S A iΛ g s hs hpoint
  letI := chartArtinStalkAlgebra S B' iΛ g s hs hpoint
  have hlin := chartArtinHom_stalkLinear S A B' f.hom iΛ g s hs hpoint
  refine ⟨{ toRingHom := f.hom.toRingHom, commutes' := ?_ }, f.isLocal, f.residue_comm⟩
  intro r
  exact congrArg (fun φ : S.presheaf.stalk s →+* B' => φ r) hlin

attribute [local instance] PredeformationConstruction.category

attribute [local implicit_reducible] Functor.Fiber BasedCategory.ofFunctor
  InducedPredeformationFunctor.toBasedFunctor

theorem isVersalAt_lift_of_base_eq
    {Y : Type v} [Category.{w} Y] (q : Y ⥤ Over S)
    (U : Over S) (x : Y) (hx : q.obj x = U) (u : U.left)
    (hv : IsVersalAt U q u x hx)
    [Algebra Λ (U.left.residueField u)]
    (i : Spec (.of Λ) ⟶ S)
    (hi : Spec.map (CommRingCat.ofHom (algebraMap Λ (U.left.residueField u))) ≫ i =
      residueFieldBasePoint U u)
    (A D : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ (U.left.residueField u))
    (f : D ⟶ A) (hf : Function.Surjective f.hom)
    (y z : Y)
    (hy : q.obj y = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ i))
    (hz : q.obj z = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ D)) ≫ i))
    (j : y ⟶ z)
    (hj : eqToHom (congrArg Over.left hy).symm ≫ (q.map j).left ≫
      eqToHom (congrArg Over.left hz) = Spec.map (CommRingCat.ofHom f.hom.toRingHom))
    (a : y ⟶ x)
    (ha : Spec.map (CommRingCat.ofHom (residueMap A)) ≫
      eqToHom (congrArg Over.left hy).symm ≫ (q.map a).left ≫
      eqToHom (congrArg Over.left hx) = U.left.fromSpecResidueField u) :
    ∃ b : z ⟶ x, j ≫ b = a := by
  let g := residueFieldBasePoint U u
  let s := basePoint U u
  let := residueFieldAlgebra U u
  have hR : Spec.map (CommRingCat.ofHom
      (algebraMap (S.presheaf.stalk s) (U.left.residueField u))) ≫
      S.fromSpecStalk s = g := Scheme.Spec_stalkClosedPointTo_fromSpecStalk g
  let A' := chartArtinObjectOverStalk S A i g s rfl hR hi
  let D' := chartArtinObjectOverStalk S D i g s rfl hR hi
  let f' : D' ⟶ A' := chartArtinHomOverStalk S D A f i g s rfl hR hi
  have hA : Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) A')) ≫
      S.fromSpecStalk s = Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ i :=
    chartArtin_base_eq_stalk S A i g s rfl hi
  have hD : Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) D')) ≫
      S.fromSpecStalk s = Spec.map (CommRingCat.ofHom (algebraMap Λ D)) ≫ i :=
    chartArtin_base_eq_stalk S D i g s rfl hi
  have hy' : q.obj y = Over.mk (Spec.map
      (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) A')) ≫ S.fromSpecStalk s) :=
    hy.trans (congrArg Over.mk hA.symm)
  have hz' : q.obj z = Over.mk (Spec.map
      (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) D')) ≫ S.fromSpecStalk s) :=
    hz.trans (congrArg Over.mk hD.symm)
  exact hv A' D' f' hf y z hy' hz' j hj a ha

end Deformation.Artin

end
