module
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.CommonBigSites
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkEquivalence.FieldFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sweep.EtaleStalkFunctor
import all StacksFrontier.AlgebraicGeometry.FundamentalGroup.SchemesEtalePoint.Basic
import StacksCore.Tactic.EgaSgaAttribute


/-!
# Étale sheaves on the spectrum of a field as continuous Galois sets

Let `K` be a field and let `sbar` be a geometric point of `Spec K`, with absolute Galois group
`G` the Galois group of the separable closure of the residue field at its image inside the
algebraically closed field of `sbar`.  Taking the stalk at `sbar` is an equivalence from the
category of sheaves of sets on the small étale site of `Spec K` to the category of sets with a
continuous `G`-action.

The Galois group acts on a stalk because it acts on the lifts of `sbar`, naturally in the
object of the site; the action is continuous because the stabilizer of a lift is open.  The
functor is fully faithful because a section is determined by its germs
(`AlgebraicGeometry.eq_of_etaleStalkGerm_eq`) and because every equivariant family of germs is
the family of germs of a section (`AlgebraicGeometry.exists_section_etaleStalkGerm`).  It is
essentially surjective because the stalk of the sheaf of equivariant maps out of the lifts of
`sbar` is the given continuous `G`-set.

## Main definitions

* `AlgebraicGeometry.ContinuousGSet.mulAction` — the underlying `G`-set of a continuous
  `G`-set, with `AlgebraicGeometry.ContinuousGSet.isOpen_stabilizer` the openness of its point
  stabilizers.
* `AlgebraicGeometry.etaleStalkSmul` — the Galois action on the étale stalk of a sheaf of sets.
* `AlgebraicGeometry.etaleStalkContinuousGSet` — that stalk as a continuous Galois set.
* `AlgebraicGeometry.etaleStalkGSetFunctor` — the resulting functor on the small étale topos.
* `AlgebraicGeometry.galoisHomSheafCounit` — the counit, evaluating a germ of an equivariant
  map at the marked lift.
* `AlgebraicGeometry.etaleStalkEquivalence` — the equivalence itself.
* `AlgebraicGeometry.etaleSheafStalkEquivalence` — the equivalence packaged with its
  identification with the stalk functor and the description of the Galois action on germs.

## Main results

* `AlgebraicGeometry.continuousSMul_etaleStalk` — the Galois action on a stalk is continuous.
* `AlgebraicGeometry.eq_of_etaleStalkGerm_eq` — a section is determined by its germs at the
  lifts of the geometric point.
* `AlgebraicGeometry.exists_section_etaleStalkGerm` — every equivariant family of germs comes
  from a section.
* `AlgebraicGeometry.galoisHomSheafCounit_bijective` — the counit is bijective.
* `AlgebraicGeometry.etaleStalkGSetFunctor_isEquivalence` — the stalk functor is an
  equivalence.
* `AlgebraicGeometry.BigEtaleSite.contains_spec_of_mk_lt` and
  `AlgebraicGeometry.nonempty_etaleStalkEquivalence_zmodTwo` — the standing hypotheses are
  jointly satisfiable, at the spectrum of a concrete finite field.

## Implementation notes

The étale stalk functor of
`StacksDraft.AlgebraicGeometry.EtaleCohomology.Fold.Sweep.EtaleStalkFunctor` is
definitionally the fiber functor of the point of the site attached to the geometric point, and
the germ map is definitionally Mathlib's `toPresheafFiber`; the colimit API of
`Mathlib.CategoryTheory.Sites.Point.Basic` is therefore used directly.  The natural
isomorphism with the stalk functor is the identity, because forgetting the Galois action from
the stalk returns the stalk on the nose.

## References

* [Stacks Project, Tag 03QT](https://stacks.math.columbia.edu/tag/03QT)
* [Stacks Project, Tag 03QR](https://stacks.math.columbia.edu/tag/03QR)
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
namespace AlgebraicGeometry
attribute [local instance] GeometricPoint.residueFieldAlgebra
attribute [local instance] geometricPointFiberMulAction

section Field
variable (B : BigEtaleSite.{u}) (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (sbar : GeometricPoint (Spec (.of K)))

/-- The point of the small étale site attached to a geometric point of the spectrum of a
field. -/
abbrev fieldSitePoint : (SmallEtale.topology B (Spec (.of K)) hK).Point.{u} :=
  geometricPointSitePoint B (Spec (.of K)) hK sbar

variable (F : smallEtaleTopos.{u, max u v} B (Spec (.of K)) hK)

/-- **The Galois action on the étale stalk of a sheaf of sets.**  A Galois automorphism moves
the germ of a section over a pointed étale neighborhood to its germ at the translated point. -/
def etaleStalkSmul (σ : GeometricPoint.absoluteGaloisGroup sbar) :
    (etaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar).obj F ⟶
      (etaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar).obj F :=
  (fieldSitePoint B K hK sbar).presheafFiberDesc
    (P := (sheafToPresheaf _ _).obj F)
    (fun U p ↦ (fieldSitePoint B K hK sbar).toPresheafFiber U
      (galoisFiberAction B K hK sbar σ p) ((sheafToPresheaf _ _).obj F))
    (fun {_X Y} f x ↦
      ((fieldSitePoint B K hK sbar).toPresheafFiber_w f
          (galoisFiberAction B K hK sbar σ x) ((sheafToPresheaf _ _).obj F)).trans
        (congrArg (fun z ↦ (fieldSitePoint B K hK sbar).toPresheafFiber Y z
          ((sheafToPresheaf _ _).obj F))
          (galoisFiberAction_naturality B K hK sbar σ f x)))

/-- The Galois action on the étale stalk, as a composite with the germ map. -/
theorem toPresheafFiber_comp_etaleStalkSmul (σ : GeometricPoint.absoluteGaloisGroup sbar)
    (U : SmallEtale B (Spec (.of K)) hK)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U) :
    (fieldSitePoint B K hK sbar).toPresheafFiber U p ((sheafToPresheaf _ _).obj F) ≫
        etaleStalkSmul.{u, v} B K hK sbar F σ =
      (fieldSitePoint B K hK sbar).toPresheafFiber U (galoisFiberAction B K hK sbar σ p)
        ((sheafToPresheaf _ _).obj F) :=
  (fieldSitePoint B K hK sbar).toPresheafFiber_presheafFiberDesc _ _ U p

/-- The Galois action on the étale stalk, computed on germs. -/
@[simp]
theorem etaleStalkSmul_germ (σ : GeometricPoint.absoluteGaloisGroup sbar)
    (U : (geometricPointFiber B (Spec (.of K)) hK sbar).Elements)
    (t : ((sheafToPresheaf _ _).obj F).obj (op U.1)) :
    ConcreteCategory.hom (etaleStalkSmul.{u, v} B K hK sbar F σ)
        (etaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar F U t) =
      etaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar F
        (Functor.elementsMk _ U.1 (galoisFiberAction B K hK sbar σ U.2)) t :=
  ConcreteCategory.congr_hom
    (toPresheafFiber_comp_etaleStalkSmul.{u, v} B K hK sbar F σ U.1 U.2) t

/-- The identity acts trivially on the étale stalk. -/
theorem etaleStalkSmul_one : etaleStalkSmul.{u, v} B K hK sbar F 1 = 𝟙 _ := by
  refine (fieldSitePoint B K hK sbar).presheafFiber_hom_ext (fun X p ↦ ?_)
  refine (toPresheafFiber_comp_etaleStalkSmul.{u, v} B K hK sbar F 1 X p).trans ?_
  refine Eq.trans (congrArg (fun z ↦ (fieldSitePoint B K hK sbar).toPresheafFiber X z
    ((sheafToPresheaf _ _).obj F)) (galoisFiberAction_one B K hK sbar p)) ?_
  exact (Category.comp_id _).symm

/-- The Galois action on the étale stalk is multiplicative. -/
theorem etaleStalkSmul_mul (σ τ : GeometricPoint.absoluteGaloisGroup sbar) :
    etaleStalkSmul.{u, v} B K hK sbar F (σ * τ) =
      etaleStalkSmul.{u, v} B K hK sbar F τ ≫ etaleStalkSmul.{u, v} B K hK sbar F σ := by
  refine (fieldSitePoint B K hK sbar).presheafFiber_hom_ext (fun X p ↦ ?_)
  refine (toPresheafFiber_comp_etaleStalkSmul.{u, v} B K hK sbar F (σ * τ) X p).trans ?_
  refine Eq.trans (congrArg (fun z ↦ (fieldSitePoint B K hK sbar).toPresheafFiber X z
    ((sheafToPresheaf _ _).obj F)) (galoisFiberAction_mul B K hK sbar σ τ p)) ?_
  refine Eq.symm (((Category.assoc _ _ _).symm).trans ?_)
  refine Eq.trans (congrArg (fun w ↦ w ≫ etaleStalkSmul.{u, v} B K hK sbar F σ)
    (toPresheafFiber_comp_etaleStalkSmul.{u, v} B K hK sbar F τ X p)) ?_
  exact toPresheafFiber_comp_etaleStalkSmul.{u, v} B K hK sbar F σ X
    (galoisFiberAction B K hK sbar τ p)

/-- The absolute Galois group acts on the étale stalk of a sheaf of sets. -/
@[instance_reducible]
def etaleStalkMulAction : MulAction (GeometricPoint.absoluteGaloisGroup sbar)
    ((etaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar).obj F) where
  smul σ x := ConcreteCategory.hom (etaleStalkSmul.{u, v} B K hK sbar F σ) x
  one_smul x := ConcreteCategory.congr_hom (etaleStalkSmul_one.{u, v} B K hK sbar F) x
  mul_smul σ τ x :=
    ConcreteCategory.congr_hom (etaleStalkSmul_mul.{u, v} B K hK sbar F σ τ) x

attribute [local instance] etaleStalkMulAction

/-- **The Galois action on the étale stalk is continuous.**  Every germ is the germ of a
section over a pointed étale neighborhood, and its stabilizer therefore contains the open
stabilizer of the marked lift. -/
theorem continuousSMul_etaleStalk :
    letI : TopologicalSpace ((etaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar).obj F) := ⊥
    ContinuousSMul (GeometricPoint.absoluteGaloisGroup sbar)
      ((etaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar).obj F) := by
  let : TopologicalSpace ((etaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar).obj F) := ⊥
  let : DiscreteTopology ((etaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar).obj F) := ⟨rfl⟩
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro x
  obtain ⟨X, p, z, hz⟩ :=
    (fieldSitePoint B K hK sbar).toPresheafFiber_jointly_surjective
      (P := (sheafToPresheaf _ _).obj F) x
  let p' : (geometricPointFiber B (Spec (.of K)) hK sbar).obj X := p
  have hle : MulAction.stabilizer (GeometricPoint.absoluteGaloisGroup sbar) p' ≤
      MulAction.stabilizer (GeometricPoint.absoluteGaloisGroup sbar) x := by
    intro σ hσ
    rw [MulAction.mem_stabilizer_iff] at hσ ⊢
    have hσ' : galoisFiberAction B K hK sbar σ p' = p' := hσ
    show ConcreteCategory.hom (etaleStalkSmul.{u, v} B K hK sbar F σ) x = x
    rw [← hz]
    exact (etaleStalkSmul_germ.{u, v} B K hK sbar F σ (Functor.elementsMk _ X (p')) z).trans
      (congrArg (fun w ↦ etaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar F (Functor.elementsMk _ X (w)) z) hσ')
  have hp : IsOpen ((MulAction.stabilizer (GeometricPoint.absoluteGaloisGroup sbar) p' :
      Subgroup (GeometricPoint.absoluteGaloisGroup sbar)) :
      Set (GeometricPoint.absoluteGaloisGroup sbar)) :=
    isOpen_stabilizer_galoisFiberAction B K hK sbar X p'
  exact Subgroup.isOpen_mono hle hp

/-- **The étale stalk of a sheaf of sets as a continuous Galois set.** -/
def etaleStalkContinuousGSet :
    AlgebraicGeometry.ContinuousGSet.{u, max u v}
      (GeometricPoint.absoluteGaloisGroup sbar) := by
  letI : HasForget₂ (Type max u v) TopCat.{max u v} :=
    { forget₂ := TopCat.discrete, forget_comp := rfl }
  letI : TopologicalSpace ((etaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar).obj F) := ⊥
  letI : DiscreteTopology ((etaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar).obj F) := ⟨rfl⟩
  exact ⟨⟨Action.ofMulAction (GeometricPoint.absoluteGaloisGroup sbar)
    ((etaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar).obj F),
    continuousSMul_etaleStalk.{u, v} B K hK sbar F⟩, ⟨rfl⟩⟩

/-- The Galois action on the étale stalk is natural in the sheaf. -/
theorem etaleStalkSmul_naturality {F F' : smallEtaleTopos.{u, max u v} B (Spec (.of K)) hK}
    (φ : F ⟶ F') (σ : GeometricPoint.absoluteGaloisGroup sbar) :
    etaleStalkSmul.{u, v} B K hK sbar F σ ≫
        (etaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar).map φ =
      (etaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar).map φ ≫
        etaleStalkSmul.{u, v} B K hK sbar F' σ := by
  refine (fieldSitePoint B K hK sbar).presheafFiber_hom_ext (fun X p ↦ ?_)
  have hL := (Category.assoc
      ((fieldSitePoint B K hK sbar).toPresheafFiber X p ((sheafToPresheaf _ _).obj F))
      (etaleStalkSmul.{u, v} B K hK sbar F σ)
      ((etaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar).map φ)).symm.trans
    ((congrArg (fun w ↦ w ≫ (etaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar).map φ)
        (toPresheafFiber_comp_etaleStalkSmul.{u, v} B K hK sbar F σ X p)).trans
      ((fieldSitePoint B K hK sbar).toPresheafFiber_naturality ((sheafToPresheaf _ _).map φ) X
        (galoisFiberAction B K hK sbar σ p)))
  have hR := (Category.assoc
      ((fieldSitePoint B K hK sbar).toPresheafFiber X p ((sheafToPresheaf _ _).obj F))
      ((etaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar).map φ)
      (etaleStalkSmul.{u, v} B K hK sbar F' σ)).symm.trans
    ((congrArg (fun w ↦ w ≫ etaleStalkSmul.{u, v} B K hK sbar F' σ)
        ((fieldSitePoint B K hK sbar).toPresheafFiber_naturality
          ((sheafToPresheaf _ _).map φ) X p)).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun w ↦ ((sheafToPresheaf _ _).map φ).app (op X) ≫ w)
          (toPresheafFiber_comp_etaleStalkSmul.{u, v} B K hK sbar F' σ X p))))
  exact hL.trans hR.symm

/-- **The étale stalk functor with its Galois action**, from the small étale topos of the
spectrum of a field to continuous sets over the absolute Galois group of a geometric point. -/
@[sga "4 VIII 2.1", sga "4 VIII 3.12" "special case", sga "7 XIII 1.2.2" "(a)"]
def etaleStalkGSetFunctor :
    smallEtaleTopos.{u, max u v} B (Spec (.of K)) hK ⥤
      AlgebraicGeometry.ContinuousGSet.{u, max u v}
        (GeometricPoint.absoluteGaloisGroup sbar) where
  obj F := etaleStalkContinuousGSet.{u, v} B K hK sbar F
  map {F F'} φ := ObjectProperty.homMk (ObjectProperty.homMk
    { hom := (etaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar).map φ
      comm := fun σ ↦ etaleStalkSmul_naturality.{u, v} B K hK sbar φ σ })
  map_id F := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    exact (etaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar).map_id F
  map_comp {F F' F''} φ ψ := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    exact (etaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar).map_comp φ ψ

/-- Morphisms to `U` with a lift of each fiber point through them generate a covering sieve. -/
private theorem ofArrows_mem_topology_of_fiber_lifts (U : SmallEtale B (Spec (.of K)) hK)
    (Z : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U → SmallEtale B (Spec (.of K)) hK)
    (g : ∀ p, Z p ⟶ U) (r : ∀ p, (geometricPointFiber B (Spec (.of K)) hK sbar).obj (Z p))
    (hr : ∀ p, (geometricPointFiber B (Spec (.of K)) hK sbar).map (g p) (r p) = p) :
    Sieve.ofArrows Z g ∈ SmallEtale.topology B (Spec (.of K)) hK U := by
  refine Stacks.EtaleCohomology.ofArrows_mem_topology B hK Z g (fun x ↦ ?_)
  obtain ⟨p, hp⟩ := exists_geometricPointFiber_base_eq B K hK sbar U x
  have h1 : (r p).1 ≫ (SmallEtale.toScheme B (Spec (.of K)) hK).map (g p) = p.1 :=
    congrArg Subtype.val (hr p)
  refine ⟨p, (r p).1.base default, ?_⟩
  have h2 : ((r p).1 ≫ (SmallEtale.toScheme B (Spec (.of K)) hK).map (g p)).base default
      = x := by rw [h1]; exact hp
  simpa using h2

/-- **A section of a sheaf on the small étale site of the spectrum of a field is determined by
its germs at the lifts of a geometric point.**  Two sections with the same germs agree after
restriction along a family of morphisms which is jointly surjective, hence covering. -/
@[sga "4 VIII 3.7" "special case"]
theorem eq_of_etaleStalkGerm_eq (F : smallEtaleTopos.{u, max u v} B (Spec (.of K)) hK)
    (U : SmallEtale B (Spec (.of K)) hK)
    (t t' : ((sheafToPresheaf _ _).obj F).obj (op U))
    (h : ∀ p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U,
      etaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar F (Functor.elementsMk _ U (p)) t =
        etaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar F (Functor.elementsMk _ U (p)) t') :
    t = t' := by
  classical
  have key : ∀ p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U,
      ∃ (Z : SmallEtale B (Spec (.of K)) hK) (g : Z ⟶ U)
        (r : (geometricPointFiber B (Spec (.of K)) hK sbar).obj Z),
        (fieldSitePoint B K hK sbar).fiber.map g r = p ∧
        ConcreteCategory.hom (((sheafToPresheaf _ _).obj F).map g.op) t =
          ConcreteCategory.hom (((sheafToPresheaf _ _).obj F).map g.op) t' := by
    intro p
    have hh := (fieldSitePoint B K hK sbar).toPresheafFiber_eq_iff'
      (P := (sheafToPresheaf _ _).obj F) U p t t'
    exact hh.mp (h p)
  choose Z g r hr hres using key
  have hcov := ofArrows_mem_topology_of_fiber_lifts B K hK sbar U Z g r hr
  have hsh := ((isSheaf_iff_isSheaf_of_type _ _).mp F.property) _ hcov
  refine hsh.isSeparatedFor.ext (fun Y f hf ↦ ?_)
  obtain ⟨W, a, b, hb, rfl⟩ := hf
  cases hb with
  | mk i =>
    simp only [op_comp, Functor.map_comp, CategoryTheory.comp_apply]
    exact ConcreteCategory.congr_arg _ (hres i)

/-- Restricting a section along a morphism of the site translates its germ to the image
lift. -/
theorem etaleStalkGerm_map (F : smallEtaleTopos.{u, max u v} B (Spec (.of K)) hK)
    {X Y : SmallEtale B (Spec (.of K)) hK} (f : X ⟶ Y)
    (x : (geometricPointFiber B (Spec (.of K)) hK sbar).obj X)
    (z : ((sheafToPresheaf _ _).obj F).obj (op Y)) :
    etaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar F (Functor.elementsMk _ X (x))
        (ConcreteCategory.hom (((sheafToPresheaf _ _).obj F).map f.op) z) =
      etaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar F
        (Functor.elementsMk _ Y ((geometricPointFiber B (Spec (.of K)) hK sbar).map f x)) z :=
  (CategoryTheory.comp_apply (((sheafToPresheaf _ _).obj F).map f.op)
      ((fieldSitePoint B K hK sbar).toPresheafFiber X x
        ((sheafToPresheaf _ _).obj F)) z).symm.trans
    (ConcreteCategory.congr_hom
      ((fieldSitePoint B K hK sbar).toPresheafFiber_w f x ((sheafToPresheaf _ _).obj F)) z)

/-- **Local existence of a section with prescribed germs.**  An equivariant family of germs
over the lifts of the geometric point is, near each lift, the family of germs of an actual
section: the prescribed germ is realized over some pointed neighborhood, which may be refined
to one whose fibre is a single Galois orbit, and equivariance then forces agreement over the
whole fibre. -/
theorem exists_local_section_etaleStalkGerm
    (F : smallEtaleTopos.{u, max u v} B (Spec (.of K)) hK)
    (U : SmallEtale B (Spec (.of K)) hK)
    (ψ : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U →
      (etaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar).obj F)
    (hψ : ∀ (σ : GeometricPoint.absoluteGaloisGroup sbar)
      (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U),
      ψ (galoisFiberAction B K hK sbar σ p) =
        ConcreteCategory.hom (etaleStalkSmul.{u, v} B K hK sbar F σ) (ψ p))
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U) :
    ∃ (W : SmallEtale B (Spec (.of K)) hK) (f : W ⟶ U)
      (y : (geometricPointFiber B (Spec (.of K)) hK sbar).obj W)
      (t : ((sheafToPresheaf _ _).obj F).obj (op W)),
      (geometricPointFiber B (Spec (.of K)) hK sbar).map f y = p ∧
      ∀ r : (geometricPointFiber B (Spec (.of K)) hK sbar).obj W,
        etaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar F (Functor.elementsMk _ W (r)) t =
          ψ ((geometricPointFiber B (Spec (.of K)) hK sbar).map f r) := by
  classical
  obtain ⟨X, x, z, hz⟩ := (fieldSitePoint B K hK sbar).toPresheafFiber_jointly_surjective
    (P := (sheafToPresheaf _ _).obj F) (ψ p)
  let A : (geometricPointFiber B (Spec (.of K)) hK sbar).Elements := (Functor.elementsMk _ X (x))
  let C : (geometricPointFiber B (Spec (.of K)) hK sbar).Elements := Functor.elementsMk _ U p
  let α : IsCofiltered.min A C ⟶ A := IsCofiltered.minToLeft A C
  let β : IsCofiltered.min A C ⟶ C := IsCofiltered.minToRight A C
  obtain ⟨V, f', q', hq', htrans⟩ := exists_transitive_refinement B K hK sbar
    (IsCofiltered.min A C).1 (IsCofiltered.min A C).2
  have hβ : (geometricPointFiber B (Spec (.of K)) hK sbar).map (f' ≫ β.1) q' = p := by
    rw [Functor.map_comp_apply, hq']
    exact β.2
  have hα : (geometricPointFiber B (Spec (.of K)) hK sbar).map (f' ≫ α.1) q' = x := by
    rw [Functor.map_comp_apply, hq']
    exact α.2
  refine ⟨V, f' ≫ β.1, q', ConcreteCategory.hom
    (((sheafToPresheaf _ _).obj F).map (f' ≫ α.1).op) z, hβ, ?_⟩
  have hbase : etaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar F (Functor.elementsMk _ V q')
      (ConcreteCategory.hom (((sheafToPresheaf _ _).obj F).map (f' ≫ α.1).op) z) = ψ p := by
    rw [etaleStalkGerm_map.{u, v} B K hK sbar F (f' ≫ α.1) q' z, hα]
    exact hz
  intro r
  obtain ⟨τ, hτ⟩ := htrans r
  have h1 : etaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar F (Functor.elementsMk _ V r)
      (ConcreteCategory.hom (((sheafToPresheaf _ _).obj F).map (f' ≫ α.1).op) z) =
      ConcreteCategory.hom (etaleStalkSmul.{u, v} B K hK sbar F τ) (ψ p) := by
    rw [← hτ, ← etaleStalkSmul_germ.{u, v} B K hK sbar F τ (Functor.elementsMk _ V q'), hbase]
  have h2 : (geometricPointFiber B (Spec (.of K)) hK sbar).map (f' ≫ β.1) r =
      galoisFiberAction B K hK sbar τ p := by
    rw [← hτ, galoisFiberAction_naturality B K hK sbar τ (f' ≫ β.1) q', hβ]
  rw [h1, h2, hψ τ p]

/-- **Every equivariant family of germs is the family of germs of a section.**  The local
sections provided by `AlgebraicGeometry.exists_local_section_etaleStalkGerm` live over a
jointly surjective, hence covering, family, and they agree on overlaps because a section is
determined by its germs; the sheaf condition then glues them. -/
theorem exists_section_etaleStalkGerm
    (F : smallEtaleTopos.{u, max u v} B (Spec (.of K)) hK)
    (U : SmallEtale B (Spec (.of K)) hK)
    (ψ : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U →
      (etaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar).obj F)
    (hψ : ∀ (σ : GeometricPoint.absoluteGaloisGroup sbar)
      (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U),
      ψ (galoisFiberAction B K hK sbar σ p) =
        ConcreteCategory.hom (etaleStalkSmul.{u, v} B K hK sbar F σ) (ψ p)) :
    ∃ t : ((sheafToPresheaf _ _).obj F).obj (op U),
      ∀ p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U,
        etaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar F (Functor.elementsMk _ U (p)) t = ψ p := by
  classical
  choose W f y tloc hy hgerm using
    exists_local_section_etaleStalkGerm.{u, v} B K hK sbar F U ψ hψ
  have hcov := ofArrows_mem_topology_of_fiber_lifts B K hK sbar U W f y hy
  have hex : ∀ ⦃Y : SmallEtale B (Spec (.of K)) hK⦄ (h : Y ⟶ U),
      (Sieve.ofArrows W f).arrows h →
      ∃ uu : ((sheafToPresheaf _ _).obj F).obj (op Y),
        ∀ r : (geometricPointFiber B (Spec (.of K)) hK sbar).obj Y,
          etaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar F (Functor.elementsMk _ Y (r)) uu =
            ψ ((geometricPointFiber B (Spec (.of K)) hK sbar).map h r) := by
    intro Y h hh
    obtain ⟨Z₀, a, b, hb, rfl⟩ := hh
    cases hb with
    | mk i =>
      refine ⟨ConcreteCategory.hom (((sheafToPresheaf _ _).obj F).map a.op) (tloc i),
        fun r ↦ ?_⟩
      rw [etaleStalkGerm_map.{u, v} B K hK sbar F a r (tloc i),
        hgerm i ((geometricPointFiber B (Spec (.of K)) hK sbar).map a r),
        Functor.map_comp_apply]
  let fam : Presieve.FamilyOfElements ((sheafToPresheaf _ _).obj F)
      (Sieve.ofArrows W f).arrows := fun _Y h hh ↦ (hex h hh).choose
  have hfam : ∀ ⦃Y : SmallEtale B (Spec (.of K)) hK⦄ (h : Y ⟶ U)
      (hh : (Sieve.ofArrows W f).arrows h)
      (r : (geometricPointFiber B (Spec (.of K)) hK sbar).obj Y),
      etaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar F (Functor.elementsMk _ Y (r)) (fam h hh) =
        ψ ((geometricPointFiber B (Spec (.of K)) hK sbar).map h r) :=
    fun _ h hh ↦ (hex h hh).choose_spec
  have hcompat : fam.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ h₁ h₂ hh₁ hh₂ hcomm
    refine eq_of_etaleStalkGerm_eq.{u, v} B K hK sbar F Z _ _ (fun r ↦ ?_)
    rw [etaleStalkGerm_map.{u, v} B K hK sbar F g₁ r (fam h₁ hh₁),
      hfam h₁ hh₁ ((geometricPointFiber B (Spec (.of K)) hK sbar).map g₁ r),
      etaleStalkGerm_map.{u, v} B K hK sbar F g₂ r (fam h₂ hh₂),
      hfam h₂ hh₂ ((geometricPointFiber B (Spec (.of K)) hK sbar).map g₂ r),
      ← Functor.map_comp_apply, ← Functor.map_comp_apply, hcomm]
  have hsh := ((isSheaf_iff_isSheaf_of_type _ _).mp F.property) _ hcov
  refine ⟨hsh.amalgamate fam hcompat, fun p ↦ ?_⟩
  obtain ⟨Y, h, hh, yy, hyy⟩ := (fieldSitePoint B K hK sbar).jointly_surjective
    (Sieve.ofArrows W f) hcov p
  have hamal : ConcreteCategory.hom (((sheafToPresheaf _ _).obj F).map h.op)
      (hsh.amalgamate fam hcompat) = fam h hh := hsh.isAmalgamation hcompat h hh
  have hyy' : (geometricPointFiber B (Spec (.of K)) hK sbar).map h yy = p := hyy
  rw [← hyy', ← etaleStalkGerm_map.{u, v} B K hK sbar F h yy, hamal, hfam h hh yy]

/-- The underlying set of the stalk with its Galois action is the stalk. -/
theorem etaleStalkGSetFunctor_comp_forget :
    etaleStalkGSetFunctor.{u, v} B K hK sbar ⋙
        AlgebraicGeometry.ContinuousGSet.forget
          (GeometricPoint.absoluteGaloisGroup sbar) =
      etaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar := rfl

/-- The map induced on stalks by a morphism of sheaves, computed on germs. -/
theorem etaleStalkFunctor_map_germ {F F' : smallEtaleTopos.{u, max u v} B (Spec (.of K)) hK}
    (φ : F ⟶ F') (U : SmallEtale B (Spec (.of K)) hK)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U)
    (t : ((sheafToPresheaf _ _).obj F).obj (op U)) :
    ConcreteCategory.hom ((etaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar).map φ)
        (etaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar F (Functor.elementsMk _ U (p)) t) =
      etaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar F' (Functor.elementsMk _ U (p))
        (ConcreteCategory.hom (((sheafToPresheaf _ _).map φ).app (op U)) t) := by
  have hnat := (fieldSitePoint B K hK sbar).toPresheafFiber_naturality
    ((sheafToPresheaf _ _).map φ) U p
  refine Eq.trans (CategoryTheory.comp_apply
    ((fieldSitePoint B K hK sbar).toPresheafFiber U p ((sheafToPresheaf _ _).obj F))
    ((etaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar).map φ) t).symm ?_
  refine Eq.trans (ConcreteCategory.congr_hom hnat t) ?_
  exact CategoryTheory.comp_apply (((sheafToPresheaf _ _).map φ).app (op U))
    ((fieldSitePoint B K hK sbar).toPresheafFiber U p ((sheafToPresheaf _ _).obj F')) t

/-- **The étale stalk functor is faithful.**  A morphism of sheaves is determined by the map it
induces on germs, and a section is determined by its germs. -/
instance etaleStalkGSetFunctor_faithful :
    (etaleStalkGSetFunctor.{u, v} B K hK sbar).Faithful where
  map_injective {F F'} {φ φ'} h := by
    have hv : (etaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar).map φ =
        (etaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar).map φ' :=
      congrArg (fun k ↦ (AlgebraicGeometry.ContinuousGSet.forget
        (GeometricPoint.absoluteGaloisGroup sbar)).map k) h
    refine ObjectProperty.hom_ext _ (NatTrans.ext ?_)
    funext Uop
    obtain ⟨U⟩ := Uop
    refine ConcreteCategory.hom_ext _ _ (fun t ↦ ?_)
    refine eq_of_etaleStalkGerm_eq.{u, v} B K hK sbar F' U _ _ (fun p ↦ ?_)
    exact (etaleStalkFunctor_map_germ.{u, v} B K hK sbar φ U p t).symm.trans
      ((ConcreteCategory.congr_hom hv
          (etaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar F (Functor.elementsMk _ U (p)) t)).trans
        (etaleStalkFunctor_map_germ.{u, v} B K hK sbar φ' U p t))

/-- **The étale stalk functor is full.**  An equivariant map of stalks prescribes, over each
object of the site, an equivariant family of germs, and every such family comes from a
section. -/
instance etaleStalkGSetFunctor_full :
    (etaleStalkGSetFunctor.{u, v} B K hK sbar).Full where
  map_surjective {F F'} h := by
    classical
    have hequiv : ∀ (σ : GeometricPoint.absoluteGaloisGroup sbar)
        (x : (etaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar).obj F),
        ConcreteCategory.hom
            ((AlgebraicGeometry.ContinuousGSet.forget
              (GeometricPoint.absoluteGaloisGroup sbar)).map h)
            (ConcreteCategory.hom (etaleStalkSmul.{u, v} B K hK sbar F σ) x) =
          ConcreteCategory.hom (etaleStalkSmul.{u, v} B K hK sbar F' σ)
            (ConcreteCategory.hom
              ((AlgebraicGeometry.ContinuousGSet.forget
                (GeometricPoint.absoluteGaloisGroup sbar)).map h) x) := fun σ x =>
      (CategoryTheory.comp_apply (etaleStalkSmul.{u, v} B K hK sbar F σ)
          ((AlgebraicGeometry.ContinuousGSet.forget
            (GeometricPoint.absoluteGaloisGroup sbar)).map h) x).symm.trans
        ((ConcreteCategory.congr_hom ((h.hom.hom).comm σ) x).trans
          (CategoryTheory.comp_apply
            ((AlgebraicGeometry.ContinuousGSet.forget
              (GeometricPoint.absoluteGaloisGroup sbar)).map h)
            (etaleStalkSmul.{u, v} B K hK sbar F' σ) x))
    have hex : ∀ (U : SmallEtale B (Spec (.of K)) hK)
        (t : ((sheafToPresheaf _ _).obj F).obj (op U)),
        ∃ t' : ((sheafToPresheaf _ _).obj F').obj (op U),
          ∀ p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U,
            etaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar F' (Functor.elementsMk _ U (p)) t' =
              ConcreteCategory.hom
                ((AlgebraicGeometry.ContinuousGSet.forget
                  (GeometricPoint.absoluteGaloisGroup sbar)).map h)
                (etaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar F (Functor.elementsMk _ U (p)) t) := by
      intro U t
      refine exists_section_etaleStalkGerm.{u, v} B K hK sbar F' U _ (fun σ p ↦ ?_)
      rw [← etaleStalkSmul_germ.{u, v} B K hK sbar F σ (Functor.elementsMk _ U (p)) t]
      exact hequiv σ _
    choose sec hsec using hex
    have hnat : ∀ (Uop Vop : (SmallEtale B (Spec (.of K)) hK)ᵒᵖ) (g : Uop ⟶ Vop),
        ((sheafToPresheaf _ _).obj F).map g ≫ (↾ (fun t ↦ sec Vop.unop t)) =
          (↾ (fun t ↦ sec Uop.unop t)) ≫ ((sheafToPresheaf _ _).obj F').map g := by
      intro Uop Vop g
      refine ConcreteCategory.hom_ext _ _ (fun t ↦ ?_)
      refine eq_of_etaleStalkGerm_eq.{u, v} B K hK sbar F' Vop.unop _ _ (fun r ↦ ?_)
      refine Eq.trans (hsec Vop.unop
        (ConcreteCategory.hom (((sheafToPresheaf _ _).obj F).map g) t) r) ?_
      refine Eq.trans (congrArg (ConcreteCategory.hom
        ((AlgebraicGeometry.ContinuousGSet.forget
          (GeometricPoint.absoluteGaloisGroup sbar)).map h))
        (etaleStalkGerm_map.{u, v} B K hK sbar F g.unop r t)) ?_
      refine Eq.trans (hsec Uop.unop t
        ((geometricPointFiber B (Spec (.of K)) hK sbar).map g.unop r)).symm ?_
      exact (etaleStalkGerm_map.{u, v} B K hK sbar F' g.unop r (sec Uop.unop t)).symm
    let φ : F ⟶ F' := ObjectProperty.homMk
      { app := fun Uop ↦ ↾ (fun t ↦ sec Uop.unop t)
        naturality := fun Uop Vop g ↦ hnat Uop Vop g }
    refine ⟨φ, ?_⟩
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    refine (fieldSitePoint B K hK sbar).presheafFiber_hom_ext (fun U p ↦ ?_)
    refine ConcreteCategory.hom_ext _ _ (fun t ↦ ?_)
    exact (CategoryTheory.comp_apply
        ((fieldSitePoint B K hK sbar).toPresheafFiber U p ((sheafToPresheaf _ _).obj F))
        ((etaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar).map φ) t).trans
      (((etaleStalkFunctor_map_germ.{u, v} B K hK sbar φ U p t).trans (hsec U t p)).trans
        (CategoryTheory.comp_apply
          ((fieldSitePoint B K hK sbar).toPresheafFiber U p ((sheafToPresheaf _ _).obj F))
          ((AlgebraicGeometry.ContinuousGSet.forget
            (GeometricPoint.absoluteGaloisGroup sbar)).map h) t).symm)

end Field

section GSet

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The underlying set of a continuous `G`-set, as a `G`-set. -/
@[instance_reducible]
def ContinuousGSet.mulAction (M : AlgebraicGeometry.ContinuousGSet.{u, v} G) :
    MulAction G M.obj.obj.V where
  smul σ x := continuousGSetSmul M σ x
  one_smul x := by
    change ConcreteCategory.hom (M.obj.obj.ρ 1).asHom x = x
    simp
  mul_smul σ τ x := by
    change ConcreteCategory.hom (M.obj.obj.ρ (σ * τ)).asHom x =
      ConcreteCategory.hom (M.obj.obj.ρ σ).asHom (ConcreteCategory.hom (M.obj.obj.ρ τ).asHom x)
    rw [map_mul]
    rfl

attribute [local instance] ContinuousGSet.mulAction

/-- **The stabilizer of a point of a continuous `G`-set is open.**  The action map is
continuous and the target is discrete. -/
theorem ContinuousGSet.isOpen_stabilizer [IsTopologicalGroup G]
    (M : AlgebraicGeometry.ContinuousGSet.{u, v} G) (x : M.obj.obj.V) :
    IsOpen ((MulAction.stabilizer G x : Subgroup G) : Set G) := by
  let : HasForget₂ (Type v) TopCat.{v} :=
    { forget₂ := TopCat.discrete, forget_comp := rfl }
  let : TopologicalSpace (M.obj.obj.V) := ⊥
  let : DiscreteTopology (M.obj.obj.V) := ⟨rfl⟩
  have hcont : Continuous (fun p : G × M.obj.obj.V ↦
      ((forget₂ (Type v) TopCat).map (M.obj.obj.ρ p.1).asHom) p.2) :=
    (Action.isContinuous_def (V := Type v) (G := G) M.obj.obj).mp M.obj.property
  have hf : Continuous (fun σ : G ↦ ConcreteCategory.hom (M.obj.obj.ρ σ).asHom x) := by
    show Continuous (fun σ ↦ ((forget₂ (Type v) TopCat).map (M.obj.obj.ρ σ).asHom) x)
    exact hcont.comp (continuous_id.prodMk continuous_const)
  have hset : ((MulAction.stabilizer G x : Subgroup G) : Set G) =
      (fun σ : G ↦ ConcreteCategory.hom (M.obj.obj.ρ σ).asHom x) ⁻¹' {x} := by
    ext σ
    simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe,
      MulAction.mem_stabilizer_iff]
    rfl
  rw [hset]
  exact (isOpen_discrete {x}).preimage hf

end GSet

section Field

attribute [local instance] ContinuousGSet.mulAction

variable (B : BigEtaleSite.{u}) (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (sbar : GeometricPoint (Spec (.of K)))

section Counit

variable (M : AlgebraicGeometry.ContinuousGSet.{u, max u v}
  (GeometricPoint.absoluteGaloisGroup sbar))

/-- **The counit of the stalk equivalence**: the germ at the geometric point of an equivariant
map out of the lifts is its value at the marked lift. -/
def galoisHomSheafCounit :
    (etaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar).obj
        (galoisGeometricPointFiberHomSheaf.{u, v} B K hK sbar M) ⟶ M.obj.obj.V :=
  (fieldSitePoint B K hK sbar).presheafFiberDesc
    (P := (sheafToPresheaf _ _).obj
      (galoisGeometricPointFiberHomSheaf.{u, v} B K hK sbar M))
    (fun _U p ↦ ↾ (fun g ↦ g.1 p))
    (fun {_X _Y} _f _x ↦ rfl)

/-- The counit of the stalk equivalence, computed on germs. -/
@[simp]
theorem galoisHomSheafCounit_germ (U : SmallEtale B (Spec (.of K)) hK)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U)
    (g : ((sheafToPresheaf _ _).obj
      (galoisGeometricPointFiberHomSheaf.{u, v} B K hK sbar M)).obj (op U)) :
    ConcreteCategory.hom (galoisHomSheafCounit.{u, v} B K hK sbar M)
        (etaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar
          (galoisGeometricPointFiberHomSheaf.{u, v} B K hK sbar M) (Functor.elementsMk _ U (p)) g) = g.1 p := by
  have hd := (fieldSitePoint B K hK sbar).toPresheafFiber_presheafFiberDesc
    (P := (sheafToPresheaf _ _).obj
      (galoisGeometricPointFiberHomSheaf.{u, v} B K hK sbar M))
    (fun _U p ↦ ↾ (fun g ↦ g.1 p)) (fun {_X _Y} _f _x ↦ rfl) U p
  exact ConcreteCategory.congr_hom hd g

/-- The counit of the stalk equivalence is equivariant. -/
theorem galoisHomSheafCounit_smul (σ : GeometricPoint.absoluteGaloisGroup sbar)
    (x : (etaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar).obj
      (galoisGeometricPointFiberHomSheaf.{u, v} B K hK sbar M)) :
    ConcreteCategory.hom (galoisHomSheafCounit.{u, v} B K hK sbar M)
        (ConcreteCategory.hom (etaleStalkSmul.{u, v} B K hK sbar
          (galoisGeometricPointFiberHomSheaf.{u, v} B K hK sbar M) σ) x) =
      σ • ConcreteCategory.hom (galoisHomSheafCounit.{u, v} B K hK sbar M) x := by
  obtain ⟨U, p, g, hg⟩ := (fieldSitePoint B K hK sbar).toPresheafFiber_jointly_surjective
    (P := (sheafToPresheaf _ _).obj
      (galoisGeometricPointFiberHomSheaf.{u, v} B K hK sbar M)) x
  have hg' : etaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar
      (galoisGeometricPointFiberHomSheaf.{u, v} B K hK sbar M) (Functor.elementsMk _ U (p)) g = x := hg
  rw [← hg', etaleStalkSmul_germ.{u, v} B K hK sbar _ σ (Functor.elementsMk _ U (p)) g,
    galoisHomSheafCounit_germ.{u, v} B K hK sbar M U _ g,
    galoisHomSheafCounit_germ.{u, v} B K hK sbar M U p g]
  exact g.2 σ p

/-- **The counit of the stalk equivalence is surjective.**  A point of a continuous Galois set
has open stabilizer, hence is fixed by the stabilizer of a lift of the geometric point to some
object of the site whose fibre is a single orbit; translating the point along the orbit defines
an equivariant map whose germ hits it. -/
theorem galoisHomSheafCounit_surjective :
    Function.Surjective
      (ConcreteCategory.hom (galoisHomSheafCounit.{u, v} B K hK sbar M)) := by
  classical
  intro m
  obtain ⟨V, q, hstab⟩ := exists_fiber_point_stabilizer_le B K hK sbar
    (MulAction.stabilizer (GeometricPoint.absoluteGaloisGroup sbar) m)
    (ContinuousGSet.isOpen_stabilizer M m)
  obtain ⟨V', f, q', hq', htrans⟩ := exists_transitive_refinement B K hK sbar V q
  have hstab' : ∀ σ : GeometricPoint.absoluteGaloisGroup sbar,
      galoisFiberAction B K hK sbar σ q' = q' → σ • m = m := by
    intro σ hσ
    refine MulAction.mem_stabilizer_iff.mp (hstab σ ?_)
    rw [← hq', ← galoisFiberAction_naturality B K hK sbar σ f q', hσ]
  have hσof : ∀ r : (geometricPointFiber B (Spec (.of K)) hK sbar).obj V',
      galoisFiberAction B K hK sbar (htrans r).choose q' = r := fun r ↦ (htrans r).choose_spec
  have hkey : ∀ (r : (geometricPointFiber B (Spec (.of K)) hK sbar).obj V')
      (σ : GeometricPoint.absoluteGaloisGroup sbar),
      galoisFiberAction B K hK sbar σ q' = r → (htrans r).choose • m = σ • m := by
    intro r σ hσ
    have h1 : galoisFiberAction B K hK sbar (σ⁻¹ * (htrans r).choose) q' = q' := by
      rw [galoisFiberAction_mul, hσof r, ← hσ, ← galoisFiberAction_mul, inv_mul_cancel,
        galoisFiberAction_one]
    have h2 := hstab' _ h1
    rwa [mul_smul, inv_smul_eq_iff] at h2
  have hφ : ∀ (σ : GeometricPoint.absoluteGaloisGroup sbar)
      (r : (geometricPointFiber B (Spec (.of K)) hK sbar).obj V'),
      (htrans (galoisFiberAction B K hK sbar σ r)).choose • m =
        continuousGSetSmul M σ ((htrans r).choose • m) := by
    intro σ r
    have h1 : galoisFiberAction B K hK sbar (σ * (htrans r).choose) q' =
        galoisFiberAction B K hK sbar σ r := by
      rw [galoisFiberAction_mul, hσof r]
    rw [hkey _ _ h1, mul_smul]
    rfl
  refine ⟨etaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar
    (galoisGeometricPointFiberHomSheaf.{u, v} B K hK sbar M) (Functor.elementsMk _ V' (q'))
    ⟨fun r ↦ (htrans r).choose • m, hφ⟩, ?_⟩
  exact (galoisHomSheafCounit_germ.{u, v} B K hK sbar M V' q'
    ⟨fun r ↦ (htrans r).choose • m, hφ⟩).trans
    ((hkey q' 1 (galoisFiberAction_one B K hK sbar q')).trans (one_smul _ m))

/-- **The counit of the stalk equivalence is injective.**  Two germs are represented over a
common pointed neighborhood, which may be refined to one whose fibre is a single Galois orbit;
two equivariant maps there which agree at the marked lift agree everywhere. -/
theorem galoisHomSheafCounit_injective :
    Function.Injective
      (ConcreteCategory.hom (galoisHomSheafCounit.{u, v} B K hK sbar M)) := by
  classical
  intro x₁ x₂ hx
  obtain ⟨X, x, z₁, z₂, h1, h2⟩ :=
    (fieldSitePoint B K hK sbar).toPresheafFiber_jointly_surjective₂
      (P := (sheafToPresheaf _ _).obj
        (galoisGeometricPointFiberHomSheaf.{u, v} B K hK sbar M)) x₁ x₂
  obtain ⟨V, f, q, hq, htrans⟩ := exists_transitive_refinement B K hK sbar X x
  have e : ∀ z : ((sheafToPresheaf _ _).obj
        (galoisGeometricPointFiberHomSheaf.{u, v} B K hK sbar M)).obj (op X),
      etaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar
          (galoisGeometricPointFiberHomSheaf.{u, v} B K hK sbar M) (Functor.elementsMk _ V (q))
          (ConcreteCategory.hom (((sheafToPresheaf _ _).obj
            (galoisGeometricPointFiberHomSheaf.{u, v} B K hK sbar M)).map f.op) z) =
        etaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar
          (galoisGeometricPointFiberHomSheaf.{u, v} B K hK sbar M) (Functor.elementsMk _ X (x)) z := by
    intro z
    rw [etaleStalkGerm_map.{u, v} B K hK sbar _ f q z, hq]
  have e1 : etaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar
      (galoisGeometricPointFiberHomSheaf.{u, v} B K hK sbar M) (Functor.elementsMk _ V (q))
      (ConcreteCategory.hom (((sheafToPresheaf _ _).obj
        (galoisGeometricPointFiberHomSheaf.{u, v} B K hK sbar M)).map f.op) z₁) = x₁ :=
    (e z₁).trans h1
  have e2 : etaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar
      (galoisGeometricPointFiberHomSheaf.{u, v} B K hK sbar M) (Functor.elementsMk _ V (q))
      (ConcreteCategory.hom (((sheafToPresheaf _ _).obj
        (galoisGeometricPointFiberHomSheaf.{u, v} B K hK sbar M)).map f.op) z₂) = x₂ :=
    (e z₂).trans h2
  have hval : (ConcreteCategory.hom (((sheafToPresheaf _ _).obj
        (galoisGeometricPointFiberHomSheaf.{u, v} B K hK sbar M)).map f.op) z₁).1 q =
      (ConcreteCategory.hom (((sheafToPresheaf _ _).obj
        (galoisGeometricPointFiberHomSheaf.{u, v} B K hK sbar M)).map f.op) z₂).1 q := by
    rwa [← galoisHomSheafCounit_germ.{u, v} B K hK sbar M V q _,
      ← galoisHomSheafCounit_germ.{u, v} B K hK sbar M V q _, e1, e2]
  have hw : ConcreteCategory.hom (((sheafToPresheaf _ _).obj
        (galoisGeometricPointFiberHomSheaf.{u, v} B K hK sbar M)).map f.op) z₁ =
      ConcreteCategory.hom (((sheafToPresheaf _ _).obj
        (galoisGeometricPointFiberHomSheaf.{u, v} B K hK sbar M)).map f.op) z₂ := by
    apply Subtype.ext
    funext r
    obtain ⟨τ, hτ⟩ := htrans r
    rw [← hτ, (ConcreteCategory.hom (((sheafToPresheaf _ _).obj
        (galoisGeometricPointFiberHomSheaf.{u, v} B K hK sbar M)).map f.op) z₁).2 τ q,
      (ConcreteCategory.hom (((sheafToPresheaf _ _).obj
        (galoisGeometricPointFiberHomSheaf.{u, v} B K hK sbar M)).map f.op) z₂).2 τ q, hval]
  rw [← e1, ← e2, hw]

/-- The counit of the stalk equivalence is bijective. -/
theorem galoisHomSheafCounit_bijective :
    Function.Bijective
      (ConcreteCategory.hom (galoisHomSheafCounit.{u, v} B K hK sbar M)) :=
  ⟨galoisHomSheafCounit_injective.{u, v} B K hK sbar M,
    galoisHomSheafCounit_surjective.{u, v} B K hK sbar M⟩

/-- The equivalence of sets underlying the counit of the stalk equivalence. -/
def galoisHomSheafCounitEquiv :
    (etaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar).obj
        (galoisGeometricPointFiberHomSheaf.{u, v} B K hK sbar M) ≃ M.obj.obj.V :=
  Equiv.ofBijective _ (galoisHomSheafCounit_bijective.{u, v} B K hK sbar M)

/-- **The stalk of the sheaf attached to a continuous Galois set is that Galois set.** -/
def galoisHomSheafCounitIso :
    (etaleStalkGSetFunctor.{u, v} B K hK sbar).obj
        (galoisGeometricPointFiberHomSheaf.{u, v} B K hK sbar M) ≅ M := by
  have hsymm : ∀ (σ : GeometricPoint.absoluteGaloisGroup sbar) (y : M.obj.obj.V),
      (galoisHomSheafCounitEquiv.{u, v} B K hK sbar M).symm (σ • y) =
        ConcreteCategory.hom (etaleStalkSmul.{u, v} B K hK sbar
          (galoisGeometricPointFiberHomSheaf.{u, v} B K hK sbar M) σ)
          ((galoisHomSheafCounitEquiv.{u, v} B K hK sbar M).symm y) := by
    intro σ y
    refine (galoisHomSheafCounitEquiv.{u, v} B K hK sbar M).injective ?_
    rw [Equiv.apply_symm_apply]
    exact ((galoisHomSheafCounit_smul.{u, v} B K hK sbar M σ
      ((galoisHomSheafCounitEquiv.{u, v} B K hK sbar M).symm y)).trans
      (congrArg (fun w ↦ σ • w)
        ((galoisHomSheafCounitEquiv.{u, v} B K hK sbar M).apply_symm_apply y))).symm
  refine ⟨ObjectProperty.homMk (ObjectProperty.homMk
      { hom := galoisHomSheafCounit.{u, v} B K hK sbar M
        comm := fun σ ↦ ConcreteCategory.hom_ext _ _ (fun x ↦ ?_) }),
    ObjectProperty.homMk (ObjectProperty.homMk
      { hom := ↾ (galoisHomSheafCounitEquiv.{u, v} B K hK sbar M).symm
        comm := fun σ ↦ ConcreteCategory.hom_ext _ _ (fun y ↦ ?_) }), ?_, ?_⟩
  · exact galoisHomSheafCounit_smul.{u, v} B K hK sbar M σ x
  · exact hsymm σ y
  · apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    refine ConcreteCategory.hom_ext _ _ (fun x ↦ ?_)
    exact (galoisHomSheafCounitEquiv.{u, v} B K hK sbar M).symm_apply_apply x
  · apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    refine ConcreteCategory.hom_ext _ _ (fun y ↦ ?_)
    exact (galoisHomSheafCounitEquiv.{u, v} B K hK sbar M).apply_symm_apply y

end Counit

/-- **The étale stalk functor is essentially surjective.**  Every continuous Galois set is the
stalk of the sheaf of equivariant maps out of the lifts of the geometric point. -/
instance etaleStalkGSetFunctor_essSurj :
    (etaleStalkGSetFunctor.{u, v} B K hK sbar).EssSurj where
  mem_essImage M :=
    ⟨galoisGeometricPointFiberHomSheaf.{u, v} B K hK sbar M,
      ⟨galoisHomSheafCounitIso.{u, v} B K hK sbar M⟩⟩

/-- The étale stalk functor from the small étale topos of `Spec K` to continuous Galois sets is
an equivalence of categories. -/
instance etaleStalkGSetFunctor_isEquivalence :
    (etaleStalkGSetFunctor.{u, v} B K hK sbar).IsEquivalence where

/-- **Stacks 03QT.**  Taking the stalk at a geometric point is an equivalence from the small
étale topos of the spectrum of a field to the category of continuous sets over the absolute
Galois group at that point. -/
@[sga "4 VIII 2.1", sga "7 XIII 1.2.2" "more general"]
def etaleStalkEquivalence :
    smallEtaleTopos.{u, max u v} B (Spec (.of K)) hK ≌
      AlgebraicGeometry.ContinuousGSet.{u, max u v}
        (GeometricPoint.absoluteGaloisGroup sbar) :=
  (etaleStalkGSetFunctor.{u, v} B K hK sbar).asEquivalence

/-- The Galois action on the stalk of a sheaf, computed on germs through the stalk
equivalence. -/
theorem etaleStalkEquivalence_rho_germ
    (F : smallEtaleTopos.{u, max u v} B (Spec (.of K)) hK)
    (σ : GeometricPoint.absoluteGaloisGroup sbar)
    (U : (geometricPointFiber B (Spec (.of K)) hK sbar).Elements)
    (t : ((sheafToPresheaf _ _).obj F).obj (op U.1)) :
    ConcreteCategory.hom
        (((etaleStalkEquivalence.{u, v} B K hK sbar).functor.obj F).obj.obj.ρ σ).asHom
        (etaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar F U t) =
      etaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar F
        (Functor.elementsMk _ U.1 (galoisFiberAction B K hK sbar σ U.2)) t :=
  etaleStalkSmul_germ.{u, v} B K hK sbar F σ U t

/-- **Stacks 03QT.**  For a geometric point of the spectrum of a field, taking stalks is an
equivalence from the small étale topos to the category of continuous sets over the absolute
Galois group, naturally identified with the stalk functor, and the Galois action on a germ
changes the geometric lift of the étale neighborhood by precomposition. -/
@[stacks 03QT,
  sga "4 VIII 2.1" "j is an equivalence",
  sga "7 XIII 1.2.2" "(a)",
  sga "7 XIII 1.1.3" "Y = Spec k"]
def etaleSheafStalkEquivalence :
    Σ e : smallEtaleTopos.{u, max u v} B (Spec (.of K)) hK ≌
        AlgebraicGeometry.ContinuousGSet.{u, max u v}
          (GeometricPoint.absoluteGaloisGroup sbar),
      { α : e.functor ⋙ AlgebraicGeometry.ContinuousGSet.forget
            (GeometricPoint.absoluteGaloisGroup sbar) ≅
          etaleStalkFunctor.{u, v} B (Spec (.of K)) hK sbar //
        ∀ (F : smallEtaleTopos.{u, max u v} B (Spec (.of K)) hK)
          (σ : GeometricPoint.absoluteGaloisGroup sbar),
          letI := GeometricPoint.residueFieldAlgebra sbar
          ∀ (τ : Gal(sbar.residueField /
              (Spec (.of K)).residueField (sbar.hom default)))
            (_hτ : ∀ a : GeometricPoint.separableClosure sbar,
              (σ a : sbar.residueField) = τ (a : sbar.residueField))
            (U : (geometricPointFiber B (Spec (.of K)) hK sbar).Elements)
            (q : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U.1)
            (_hq : q.1 = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ U.2.1)
            (t : ((sheafToPresheaf _ _).obj F).obj (op U.1)),
            let V : (geometricPointFiber B (Spec (.of K)) hK sbar).Elements := Functor.elementsMk _ U.1 q
            ConcreteCategory.hom (α.app F).hom
                (ConcreteCategory.hom ((e.functor.obj F).obj.obj.ρ σ).asHom
                  (ConcreteCategory.hom (α.app F).inv
                    (etaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar F U t))) =
              etaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar F V t } := by
  refine ⟨etaleStalkEquivalence.{u, v} B K hK sbar, Iso.refl _, ?_⟩
  intro F σ τ hτ U q hq t
  have hqa : galoisFiberAction B K hK sbar σ U.2 = q := by
    apply Subtype.ext
    rw [coe_galoisFiberAction_of_extends B K hK sbar σ τ.toRingHom
      (fun a ↦ (hτ a).symm) U.2, hq]
  exact (etaleStalkEquivalence_rho_germ.{u, v} B K hK sbar F σ U t).trans
    (congrArg (fun w ↦ etaleStalkGerm.{u, v} B (Spec (.of K)) hK sbar F (Functor.elementsMk _ U.1 w) t) hqa)

/-! ### Non-vacuity of the standing hypotheses -/

/-- The spectrum of a ring of cardinality below the cutoff of a big étale site is an object of
that site. -/
theorem BigEtaleSite.contains_spec_of_mk_lt (B : BigEtaleSite.{u}) (R : CommRingCat.{u})
    (h : Cardinal.mk R < B.cutoff) : B.Contains (Spec R) := by
  show (Spec R).size < B.cutoff
  rw [Scheme.size_Spec R]
  exact max_lt B.aleph0_lt_cutoff h

/-- The algebraic closure of a field is a geometric point of its spectrum. -/
def GeometricPoint.ofAlgebraicClosure (K : Type u) [Field K] :
    GeometricPoint (Spec (.of K)) where
  residueField := AlgebraicClosure K
  hom := Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))

/-- **The standing hypotheses of `AlgebraicGeometry.etaleSheafStalkEquivalence` are jointly
satisfiable.**  A big étale site exists, its cutoff exceeds `ℵ₀` and hence the size of the
spectrum of any finite field, and the algebraic closure supplies a geometric point. -/
theorem nonempty_etaleStalkEquivalence_zmodTwo :
    ∃ (B : BigEtaleSite.{0}) (hK : B.Contains (Spec (.of (ZMod 2)))),
    Nonempty (smallEtaleTopos.{0, 0} B (Spec (.of (ZMod 2))) hK ≌
      AlgebraicGeometry.ContinuousGSet.{0, 0}
        (GeometricPoint.absoluteGaloisGroup
          (GeometricPoint.ofAlgebraicClosure (ZMod 2)))) := by
  obtain ⟨B, -⟩ := exists_common_bigEtaleSite (fun i : PEmpty.{1} ↦ i.elim)
  have hK : B.Contains (Spec (.of (ZMod 2))) := B.contains_spec_of_mk_lt _
    ((Cardinal.lt_aleph0_of_finite _).trans_le B.aleph0_lt_cutoff.le)
  exact ⟨B, hK, ⟨etaleStalkEquivalence.{0, 0} B (ZMod 2) hK
    (GeometricPoint.ofAlgebraicClosure (ZMod 2))⟩⟩

end Field

/-! ### Section 59.56, the Galois action on stalks

Tag 03QW is the section itself and has no statement of its own: it constructs the action of
`Aut(κ(s̄)/κ(s))` on the stalk at a geometric point `s̄` over a point `s` of a scheme, checks
that it is a left action and functorial in the sheaf, and observes that it factors through the
absolute Galois group `Gal_{κ(s)}`, so that the stalk functor lands in `Gal_{κ(s)}`-sets. The
declarations above are that content for the spectrum of a field, and the tag is recorded
against them below rather than restated. For an arbitrary scheme the action at a rational
point is `Stacks.Frobenius.galoisStalkAction`, which carries the tag in its own file.

The factoring through the absolute Galois group is definitional here, the action being
constructed for `GeometricPoint.absoluteGaloisGroup` directly rather than for the full
automorphism group of the extension; and the general case of a point of an arbitrary scheme
whose residue field is not the base is not available.
-/

add_to_stacks 03QW "the Galois action on an étale stalk, for the spectrum of a field only"
  AlgebraicGeometry.etaleStalkSmul
add_to_stacks 03QW "the rule 59.56.0.1 on germs, for the spectrum of a field only"
  AlgebraicGeometry.etaleStalkSmul_germ
add_to_stacks 03QW "the identity acts trivially, for the spectrum of a field only"
  AlgebraicGeometry.etaleStalkSmul_one
add_to_stacks 03QW "multiplicativity of the action, for the spectrum of a field only"
  AlgebraicGeometry.etaleStalkSmul_mul
add_to_stacks 03QW "the left action on the stalk, for the spectrum of a field only"
  AlgebraicGeometry.etaleStalkMulAction
add_to_stacks 03QW "functoriality of the action in the sheaf, for the spectrum of a field only"
  AlgebraicGeometry.etaleStalkSmul_naturality
add_to_stacks 03QW "continuity of the action, for the spectrum of a field only"
  AlgebraicGeometry.continuousSMul_etaleStalk
add_to_stacks 03QW "the stalk as a continuous Galois set, for the spectrum of a field only"
  AlgebraicGeometry.etaleStalkContinuousGSet
add_to_stacks 03QW "the stalk functor to continuous Galois sets, for a field only"
  AlgebraicGeometry.etaleStalkGSetFunctor

end AlgebraicGeometry
end
