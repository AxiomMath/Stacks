module

public import StacksFrontier.Deformation.Examples.Geometric.SpacesSpecialFibreThickening
public import StacksFrontier.Deformation.Examples.Geometric.SpacesInfinitesimalAutomorphismsConormalPrincipal
public import StacksFrontier.Deformation.Examples.Geometric.SpacesInfinitesimalAutomorphismsFlatAnnihilator
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkAsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffinePushforwardExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFunctorial
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdeals
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartBaseChangePresieve
public import StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceDerivation
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# The conormal module of the special fibre of a deformation over the dual numbers

Let `A` be an object of `𝒞_Λ` with an element `ε` generating the kernel of the residue map and
whose annihilator is `εA` (the dual numbers `k[ε]`), and let `X'` be an algebraic space flat
over `Spec A`, with special fibre `G ⊆ X'` the inverse image of `Spec k ⊂ Spec A`.  Then the
conormal module of `G` in `X'` is free of rank one,

`𝒞_{G/X'} ≅ 𝒪_G`.

Multiplication by the pullback `t` of `ε` is a map `𝒪_{X'} ⟶ 𝓘_G`: on every affine étale chart
`U` of `X'` the defining ideal is `t·𝒪(U)`, the ideal of `Spec k` in `Spec A` being `εA`
(`AlgebraicGeometry.Space.definingIdealAt_preimage_eq_map_chartDiagram`), so it is surjective;
and its kernel is `𝓘_G`, because `𝒪(U)` is flat over `A` and the annihilator of `ε` is `εA`
(`Algebra.mem_span_singleton_of_flat_of_mul_eq_zero`).  So it is a cokernel of `𝓘_G ⟶ 𝒪_{X'}`,
and `AlgebraicGeometry.Space.conormalModuleIsoUnitOfIsColimit` applies.

## Main definitions

* `Deformation.Examples.familyChartDiagram`: an étale chart of `X'` over the identity chart of
  `Spec A`.
* `Deformation.Examples.familyChartScalar`: the pullback `t` of `ε` to an étale chart.
* `Deformation.Examples.spaceSpecialConormalIsoUnit`: `𝒞_{G/X'} ≅ 𝒪_G`.

## References

* [Stacks Project, Tag 0E41](https://stacks.math.columbia.edu/tag/0E41)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Space

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 5000] SheafOfModules.instAbelian

namespace Deformation.Examples

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ)))
variable (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))
variable (P : FlatAlgebraicSpaceFamily B hΛ hSpec)

/-- The identity chart of `Spec A`, as an étale chart of the algebraic space it represents. -/
abbrev baseIdChart (A : ArtinianLocalAlgCat.{u, u, u} Λ k) :
    SmallEtale B (Spec (.of Λ)) hΛ (schemeSpace (spaceBaseOver B hΛ hSpec A)).1 :=
  idChart B (Spec (.of Λ)) hΛ (spaceBaseOver B hΛ hSpec A)

/-- The morphism of an étale chart of the total space of a family to `Spec` of its base. -/
def familyChartToBase (U : SmallEtale B (Spec (.of Λ)) hΛ P.space) :
    (SmallEtale.toOver B (Spec (.of Λ)) hΛ P.space).obj U ⟶ spaceBaseOver B hΛ hSpec P.base :=
  yoneda.preimage (U.obj.hom ≫ P.toBase)

/-- **An étale chart of the total space over the identity chart of `Spec A`.** -/
def familyChartDiagram (U : SmallEtale B (Spec (.of Λ)) hΛ P.space) :
    ChartDiagram B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P).1
      (schemeSpace (spaceBaseOver B hΛ hSpec P.base)).1 (spaceTotalToBase B hΛ hSpec P).hom where
  U := U
  V := baseIdChart B hΛ hSpec P.base
  g := familyChartToBase B hΛ hSpec P U
  comm := by
    change U.obj.hom ≫ P.toBase = yoneda.map (familyChartToBase B hΛ hSpec P U) ≫ 𝟙 _
    rw [Category.comp_id, familyChartToBase, Functor.map_preimage]

/-- An element of the base ring, as a function on `Spec A`. -/
def baseFunction (a : P.base) :
    ToType ((structureRingSheaf B (Spec (.of Λ)) hΛ
      (schemeSpace (spaceBaseOver B hΛ hSpec P.base))).obj.obj
        (op (baseIdChart B hΛ hSpec P.base))) :=
  (Scheme.ΓSpecIso (CommRingCat.of P.base)).inv.hom a

/-- **The pullback of an element of the base ring to an étale chart of the total space.** -/
def familyChartScalar (U : SmallEtale B (Spec (.of Λ)) hΛ P.space) (a : P.base) :
    ToType ((structureRingSheaf B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)).obj.obj
      (op U)) :=
  (chartDiagramPullback B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
    (familyChartDiagram B hΛ hSpec P U)).hom (baseFunction B hΛ hSpec P a)

/-- The pullbacks of an element of the base ring are compatible with restriction. -/
theorem familyChartScalar_map {U V : SmallEtale B (Spec (.of Λ)) hΛ P.space} (g : V ⟶ U)
    (a : P.base) :
    ((structureRingSheaf B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)).obj.map g.op).hom
        (familyChartScalar B hΛ hSpec P U a) = familyChartScalar B hΛ hSpec P V a := by
  have hg : (SmallEtale.toOver B (Spec (.of Λ)) hΛ P.space).map g ≫
      familyChartToBase B hΛ hSpec P U = familyChartToBase B hΛ hSpec P V := by
    apply yoneda.map_injective
    rw [Functor.map_comp, familyChartToBase, familyChartToBase, Functor.map_preimage,
      Functor.map_preimage, ← Category.assoc]
    exact congrArg (· ≫ P.toBase)
      (CostructuredArrow.w ((SmallEtale.inclusion B (Spec (.of Λ)) hΛ P.space).map g))
  change (Scheme.Γ.map ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
      ((SmallEtale.toOver B (Spec (.of Λ)) hΛ P.space).map g)).op).hom
      ((Scheme.Γ.map ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
        (familyChartToBase B hΛ hSpec P U)).op).hom (baseFunction B hΛ hSpec P a)) =
    (Scheme.Γ.map ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
      (familyChartToBase B hΛ hSpec P V)).op).hom (baseFunction B hΛ hSpec P a)
  rw [← hg, Functor.map_comp, op_comp, Functor.map_comp]
  rfl

/-- The kernel of the map on functions of a morphism to `Spec A` factoring as an isomorphism
followed by `Spec k ⟶ Spec A` is the kernel of the residue map. -/
theorem ker_Γ_map_of_eq_comp (f : P.base ⟶ residueFieldBase Λ k)
    {W : BigFppfOver B (Spec (.of Λ)) hΛ} (s : W ⟶ spaceBaseOver B hΛ hSpec P.base)
    (φ : W ⟶ spaceBaseOver B hΛ hSpec (residueFieldBase Λ k))
    (hφ : IsIso φ) (hs : s = φ ≫ spaceBaseOverMap B hΛ hSpec f) :
    RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map s).op).hom =
      Ideal.map (Scheme.ΓSpecIso (CommRingCat.of P.base)).inv.hom
        (RingHom.ker f.hom.toRingHom) := by
  subst hs
  have hinj : Function.Injective (Scheme.Γ.map
      ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map φ).op).hom :=
    (ConcreteCategory.bijective_of_isIso _).1
  rw [Functor.map_comp, op_comp, Functor.map_comp, CommRingCat.hom_comp,
    RingHom.ker_comp_of_injective _ hinj, toScheme_map_spaceBaseOverMap, Scheme.Γ_map_op]
  refine (Stacks.Smooth.ker_specMap_appTop (CommRingCat.ofHom f.hom.toRingHom)).trans ?_
  rw [CommRingCat.hom_ofHom]
  exact (Ideal.map_comap_of_equiv
    (Scheme.ΓSpecIso (CommRingCat.of P.base)).symm.commRingCatIsoToRingEquiv).symm

/-- **The ideal of `Spec k` in `Spec A` on the identity chart** is the kernel of the residue map,
read through `Γ(Spec A) ≅ A`. -/
theorem definingIdealAt_baseSpecial_idChart (f : P.base ⟶ residueFieldBase Λ k) :
    definingIdealAt B (Spec (.of Λ)) hΛ (schemeSpace (spaceBaseOver B hΛ hSpec P.base))
        (spaceBaseSpecialSubspace B hΛ hSpec f) (op (baseIdChart B hΛ hSpec P.base)) =
      Ideal.map (Scheme.ΓSpecIso (CommRingCat.of P.base)).inv.hom
        (RingHom.ker f.hom.toRingHom) := by
  let K := spaceBaseSpecialSubspace B hΛ hSpec f
  let j := yoneda.map (spaceBaseOverMap B hΛ hSpec f)
  let hf := K.2.2.rep
  let h := (baseIdChart B hΛ hSpec P.base).obj.hom
  have hfst : IsIso (hf.fst h) := (hf.isPullback h).isIso_fst_of_isIso (by
    change IsIso (𝟙 (yoneda.obj (spaceBaseOver B hΛ hSpec P.base)))
    exact IsIso.id _)
  have hmono : Mono j := by
    have hm : Mono ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
        (spaceBaseOverMap B hΛ hSpec f)) := by
      rw [toScheme_map_spaceBaseOverMap]
      have := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom f.hom.toRingHom)
        (surjective_of_hom_residueFieldBase f)
      infer_instance
    have : Mono (spaceBaseOverMap B hΛ hSpec f) :=
      (BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).mono_of_mono_map hm
    exact yoneda.map_mono _
  have htr : IsIso (Subfunctor.toRange j) := inferInstance
  let φ := yoneda.preimage (hf.fst h ≫ @inv _ _ _ _ (Subfunctor.toRange j) htr)
  have hφ : IsIso φ := by
    have : IsIso (yoneda.map φ) := by
      rw [Functor.map_preimage]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ hfst (@IsIso.inv_isIso _ _ _ _ _ htr)
    exact isIso_of_fully_faithful yoneda φ
  have hsnd : hf.snd h = φ ≫ spaceBaseOverMap B hΛ hSpec f := by
    apply yoneda.map_injective
    have hw : hf.fst h ≫ (Subfunctor.range j).ι = yoneda.map (hf.snd h) ≫ h := hf.w h
    have h3 : (Subfunctor.range j).ι =
        @inv _ _ _ _ (Subfunctor.toRange j) htr ≫ j :=
      ((IsIso.inv_hom_id_assoc (Subfunctor.toRange j) (Subfunctor.range j).ι).symm).trans
        (congrArg (@inv _ _ _ _ (Subfunctor.toRange j) htr ≫ ·) (Subfunctor.toRange_ι j))
    refine ((hw.trans (Category.comp_id _)).symm.trans ?_).trans
      (Functor.map_comp yoneda φ (spaceBaseOverMap B hΛ hSpec f)).symm
    rw [h3]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ j) (Functor.map_preimage yoneda _).symm)
  rw [definingIdealAt_eq_ker B (Spec (.of Λ)) hΛ _ K (baseIdChart B hΛ hSpec P.base)]
  exact ker_Γ_map_of_eq_comp B hΛ hSpec P f _ φ hφ hsnd

/-! ### The special fibre is cut out by `ε` -/

/-- The rings of sections of the structure sheaf of an algebraic space are commutative. -/
@[reducible] def structureRingSheafCommRing (X : AlgebraicSpaces B (Spec (.of Λ)) hΛ)
    (U : (SmallEtale B (Spec (.of Λ)) hΛ X.1)ᵒᵖ) :
    CommRing (ToType ((structureRingSheaf B (Spec (.of Λ)) hΛ X).obj.obj U)) :=
  inferInstanceAs
    (CommRing (ToType ((smallEtaleRingedSite B (Spec (.of Λ)) hΛ X.1 X.2).O.obj.obj U)))

attribute [local instance] structureRingSheafCommRing

section Epsilon

variable (f : P.base ⟶ residueFieldBase Λ k) (εA : P.base)
  (hk : RingHom.ker f.hom.toRingHom = Ideal.span {εA})

/-- The ring homomorphism `A ⟶ 𝒪(U)` of an étale chart of the total space. -/
def familyChartRingHom (U : SmallEtale B (Spec (.of Λ)) hΛ P.space) :
    P.base →+* Γ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).obj U.1.left, ⊤) :=
  (Scheme.Γ.map ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
    (familyChartToBase B hΛ hSpec P U)).op).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of P.base)).inv.hom

/-- The ring homomorphism `familyChartRingHom` sends `a` to its scalar `familyChartScalar` on the
chart `U`. -/
theorem familyChartRingHom_apply (U : SmallEtale B (Spec (.of Λ)) hΛ P.space) (a : P.base) :
    familyChartRingHom B hΛ hSpec P U a = familyChartScalar B hΛ hSpec P U a :=
  rfl

include hk in
/-- **On an affine étale chart `U` of the total space, the ideal of the special fibre is
generated by the pullback of `ε`.** -/
theorem definingIdealAt_spaceSpecialSubspace_affine (U : SmallEtale B (Spec (.of Λ)) hΛ P.space)
    [IsAffine ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).obj U.1.left)] :
    definingIdealAt B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
        (spaceSpecialSubspace B hΛ hSpec P f) (op U) =
      Ideal.span {familyChartScalar B hΛ hSpec P U εA} := by
  have : IsAffine ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).obj
      (familyChartDiagram B hΛ hSpec P U).V.1.left) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of P.base)))
  have : IsAffine ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).obj
      (familyChartDiagram B hΛ hSpec P U).U.1.left) :=
    inferInstanceAs (IsAffine ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).obj U.1.left))
  refine (definingIdealAt_preimage_eq_map_chartDiagram B (Spec (.of Λ)) hΛ
    (spaceTotalToBase B hΛ hSpec P) (spaceBaseSpecialSubspace B hΛ hSpec f)
    (familyChartDiagram B hΛ hSpec P U)).trans ?_
  have h : definingIdealAt B (Spec (.of Λ)) hΛ (schemeSpace (spaceBaseOver B hΛ hSpec P.base))
      (spaceBaseSpecialSubspace B hΛ hSpec f) (op (familyChartDiagram B hΛ hSpec P U).V) =
      Ideal.map (Scheme.ΓSpecIso (CommRingCat.of P.base)).inv.hom
        (RingHom.ker f.hom.toRingHom) :=
    definingIdealAt_baseSpecial_idChart B hΛ hSpec P f
  refine (congrArg (Ideal.map (chartDiagramPullback B (Spec (.of Λ)) hΛ
    (spaceTotalToBase B hΛ hSpec P) (familyChartDiagram B hΛ hSpec P U)).hom) h).trans ?_
  refine (congrArg (Ideal.map (chartDiagramPullback B (Spec (.of Λ)) hΛ
    (spaceTotalToBase B hΛ hSpec P) (familyChartDiagram B hΛ hSpec P U)).hom)
    ((congrArg (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of P.base)).inv.hom) hk).trans
      (Ideal.map_span _ _))).trans ?_
  refine (Ideal.map_span _ _).trans ?_
  exact congrArg Ideal.span ((congrArg (Set.image _) (Set.image_singleton)).trans
    Set.image_singleton)

/-- Membership in the ideal of the special fibre can be checked after restricting to affine
étale charts. -/
private theorem mem_definingIdealAt_spaceSpecialSubspace_of_affine
    (U : SmallEtale B (Spec (.of Λ)) hΛ P.space)
    (x : ToType ((structureRingSheaf B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)).obj.obj
      (op U)))
    (h : ∀ (W : SmallEtale B (Spec (.of Λ)) hΛ P.space)
      (_ : IsAffine ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).obj W.1.left)) (b : W ⟶ U),
      ((structureRingSheaf B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)).obj.map b.op).hom
        x ∈ definingIdealAt B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
          (spaceSpecialSubspace B hΛ hSpec P f) (op W)) :
    x ∈ definingIdealAt B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
      (spaceSpecialSubspace B hΛ hSpec P f) (op U) := by
  refine mem_definingIdealAt_of_sieve B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
    (spaceSpecialSubspace B hΛ hSpec P f) (op U) x _
    (SmallEtale.generate_affineChartPresieve_mem B (Spec (.of Λ)) hΛ P.space U) ?_
  rintro V g ⟨W, a, b, hW, rfl⟩
  have h1 := definingIdealAt_map B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
    (spaceSpecialSubspace B hΛ hSpec P f) a.op _ (h W hW b)
  rw [op_comp, Functor.map_comp]
  exact h1

include hk in
/-- **The pullback of `ε` lies in the ideal of the special fibre** on every étale chart. -/
theorem familyChartScalar_mem_definingIdealAt (U : SmallEtale B (Spec (.of Λ)) hΛ P.space) :
    familyChartScalar B hΛ hSpec P U εA ∈ definingIdealAt B (Spec (.of Λ)) hΛ
      (spaceTotalSpace B hΛ hSpec P) (spaceSpecialSubspace B hΛ hSpec P f) (op U) := by
  have key : ∀ (W : SmallEtale B (Spec (.of Λ)) hΛ P.space)
      (_ : IsAffine ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).obj W.1.left)),
      familyChartScalar B hΛ hSpec P W εA ∈ definingIdealAt B (Spec (.of Λ)) hΛ
        (spaceTotalSpace B hΛ hSpec P) (spaceSpecialSubspace B hΛ hSpec P f) (op W) := by
    intro W hW
    rw [definingIdealAt_spaceSpecialSubspace_affine B hΛ hSpec P f εA hk W]
    exact Ideal.mem_span_singleton_self _
  refine mem_definingIdealAt_spaceSpecialSubspace_of_affine B hΛ hSpec P f U _ fun W hW b => ?_
  rw [familyChartScalar_map B hΛ hSpec P b εA]
  exact key W hW

include hk in
/-- **Multiplication by `ε`**, as a map from the structure sheaf of the total space to the ideal
of the special fibre. -/
def specialEpsilonMul :
    SheafOfModules.unit (structureRingSheaf B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)) ⟶
      (definingIdealSheaf B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
        (spaceSpecialSubspace B hΛ hSpec P f)).toSheafOfModules where
  val :=
    { app := fun U =>
        letI : CommRing ↑((structureRingSheaf B (Spec (.of Λ)) hΛ
            (spaceTotalSpace B hΛ hSpec P)).obj.obj U) :=
          inferInstanceAs (CommRing ((smallEtaleRingedSite B (Spec (.of Λ)) hΛ P.space
            P.algebraic).O.obj.obj U))
        ModuleCat.ofHom
          { toFun := fun x => ⟨familyChartScalar B hΛ hSpec P U.unop εA *
                (show ToType ((structureRingSheaf B (Spec (.of Λ)) hΛ
                  (spaceTotalSpace B hΛ hSpec P)).obj.obj U) from x), by
              rw [mul_comm]
              exact Ideal.mul_mem_left _ x
                (familyChartScalar_mem_definingIdealAt B hΛ hSpec P f εA hk U.unop)⟩
            map_add' := fun x y => Subtype.ext (mul_add _ x y)
            map_smul' := fun r x => Subtype.ext (mul_left_comm _ r x) }
      naturality := fun {U V} g => by
        refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
        let y : ToType ((structureRingSheaf B (Spec (.of Λ)) hΛ
          (spaceTotalSpace B hΛ hSpec P)).obj.obj U) := x
        change familyChartScalar B hΛ hSpec P V.unop εA *
            ((structureRingSheaf B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)).obj.map
              g).hom y =
          ((structureRingSheaf B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)).obj.map
            g).hom (familyChartScalar B hΛ hSpec P U.unop εA * y)
        rw [map_mul, ← familyChartScalar_map B hΛ hSpec P g.unop εA]
        rfl }

omit hk in
/-- **The functions on an affine étale chart of the total space are flat over the base**: the
chart morphism to `Spec A` is flat, the family being flat. -/
theorem familyChartRingHom_flat (U : SmallEtale B (Spec (.of Λ)) hΛ P.space)
    [IsAffine ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).obj U.1.left)] :
    (familyChartRingHom B hΛ hSpec P U).Flat := by
  have hfl : Flat ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
      (familyChartToBase B hΛ hSpec P U)) :=
    P.flat U.obj.left (spaceBaseOver B hΛ hSpec P.base) U.obj.hom (𝟙 _)
      (familyChartToBase B hΛ hSpec P U) U.2
      (presheaf_etale_id B (Spec (.of Λ)) hΛ (spaceBaseOver B hΛ hSpec P.base))
      (by rw [Category.comp_id, familyChartToBase, Functor.map_preimage])
  have : IsAffine ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).obj
      (spaceBaseOver B hΛ hSpec P.base)) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of P.base)))
  have : IsAffine ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).obj
      ((SmallEtale.toOver B (Spec (.of Λ)) hΛ P.space).obj U)) :=
    inferInstanceAs (IsAffine ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).obj U.1.left))
  exact RingHom.Flat.comp (.of_bijective (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of P.base)).inv))
    (Scheme.Hom.flat_appTop ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
      (familyChartToBase B hΛ hSpec P U)))

include hk in
/-- **The annihilator of `ε` is the ideal of the special fibre**, on every étale chart: on an
affine chart because the functions there are flat over `A`, and in general locally. -/
theorem mem_definingIdealAt_of_familyChartScalar_mul_eq_zero
    (hann : ∀ a : P.base, εA * a = 0 ↔ a ∈ Ideal.span {εA})
    (U : SmallEtale B (Spec (.of Λ)) hΛ P.space)
    (x : ToType ((structureRingSheaf B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)).obj.obj
      (op U)))
    (hx : familyChartScalar B hΛ hSpec P U εA * x = 0) :
    x ∈ definingIdealAt B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
      (spaceSpecialSubspace B hΛ hSpec P f) (op U) := by
  have key : ∀ (W : SmallEtale B (Spec (.of Λ)) hΛ P.space)
      (_ : IsAffine ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).obj W.1.left))
      (y : ToType ((structureRingSheaf B (Spec (.of Λ)) hΛ
        (spaceTotalSpace B hΛ hSpec P)).obj.obj (op W)))
      (_ : familyChartScalar B hΛ hSpec P W εA * y = 0),
      y ∈ definingIdealAt B (Spec (.of Λ)) hΛ
        (spaceTotalSpace B hΛ hSpec P) (spaceSpecialSubspace B hΛ hSpec P f) (op W) := by
    intro W hW y hy
    rw [definingIdealAt_spaceSpecialSubspace_affine B hΛ hSpec P f εA hk W]
    let := (familyChartRingHom B hΛ hSpec P W).toAlgebra
    have : Module.Flat P.base Γ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).obj W.1.left, ⊤) :=
      familyChartRingHom_flat B hΛ hSpec P W
    exact Algebra.mem_span_singleton_of_flat_of_mul_eq_zero
      (R := Γ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).obj W.1.left, ⊤)) εA hann y hy
  refine mem_definingIdealAt_spaceSpecialSubspace_of_affine B hΛ hSpec P f U x fun W hW b => ?_
  refine key W hW _ ?_
  rw [← familyChartScalar_map B hΛ hSpec P b εA, ← map_mul, hx, map_zero]

include hk in
/-- Multiplication by `ε` kills the ideal of the special fibre, which has square zero. -/
theorem definingIdealSheaf_ι_comp_specialEpsilonMul
    (hG : IsFirstOrderThickening B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
      (spaceSpecialSubspace B hΛ hSpec P f).1) :
    (definingIdealSheaf B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
      (spaceSpecialSubspace B hΛ hSpec P f)).ι ≫ specialEpsilonMul B hΛ hSpec P f εA hk = 0 := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_))
  let y : ToType ((structureRingSheaf B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)).obj.obj
    U) := x.1
  change familyChartScalar B hΛ hSpec P U.unop εA * y = 0
  exact mul_eq_zero_of_mem_definingIdealAt B (Spec (.of Λ)) hΛ
    (spaceSpecialSubspace B hΛ hSpec P f) hG
    (familyChartScalar_mem_definingIdealAt B hΛ hSpec P f εA hk U.unop) x.2

variable (hann : ∀ a : P.base, εA * a = 0 ↔ a ∈ Ideal.span {εA})
  (hG : IsFirstOrderThickening B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
      (spaceSpecialSubspace B hΛ hSpec P f).1)

include hann in
/-- **The ideal of the special fibre is the kernel of multiplication by `ε`.** -/
def isLimitSpecialEpsilonMul :
    IsLimit (KernelFork.ofι (definingIdealSheaf B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
      (spaceSpecialSubspace B hΛ hSpec P f)).ι
      (definingIdealSheaf_ι_comp_specialEpsilonMul B hΛ hSpec P f εA hk hG)) :=
  KernelFork.IsLimit.ofι _ _
    (fun {W} g hg =>
      { val :=
          { app := fun U => ModuleCat.ofHom
              { toFun := fun w => ⟨(g.val.app U).hom w,
                  mem_definingIdealAt_of_familyChartScalar_mul_eq_zero B hΛ hSpec P f εA hk hann
                    U.unop _ (by exact congrArg (fun φ => ((φ.val.app U).hom w).1) hg)⟩
                map_add' := fun x y => Subtype.ext ((g.val.app U).hom.map_add x y)
                map_smul' := fun r x => Subtype.ext ((g.val.app U).hom.map_smul r x) }
            naturality := fun {U V} q => ModuleCat.hom_ext (LinearMap.ext fun x =>
              Subtype.ext (congrArg (fun φ => φ.hom x) (g.val.naturality q))) } })
    (fun {W} g hg => SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun _ => rfl))
    (fun {W} g hg φ hφ => by
      apply (cancel_mono (definingIdealSheaf B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
        (spaceSpecialSubspace B hΛ hSpec P f)).ι).1
      exact hφ.trans (SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun _ => rfl)))

/-- **Multiplication by `ε` is surjective onto the ideal of the special fibre**, on every affine
chart. -/
theorem epi_specialEpsilonMul :
    Epi (specialEpsilonMul B hΛ hSpec P f εA hk) := by
  refine epi_of_surjective_affineChartDiagram (spaceTotalToBase B hΛ hSpec P)
    _ (fun d hU _ => ?_)
  have : IsAffine ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).obj d.U.1.left) := hU
  rintro ⟨y, hy⟩
  let y' : ToType ((structureRingSheaf B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)).obj.obj
    (op d.U)) := y
  have hy' : y' ∈ Ideal.span {familyChartScalar B hΛ hSpec P d.U εA} := by
    rwa [← definingIdealAt_spaceSpecialSubspace_affine B hΛ hSpec P f εA hk d.U]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hy'
  refine ⟨c, Subtype.ext ?_⟩
  change familyChartScalar B hΛ hSpec P d.U εA * c = y'
  let : CommRing (ToType ((structureRingSheaf B (Spec (.of Λ)) hΛ
      (spaceTotalSpace B hΛ hSpec P)).obj.obj (op d.U))) :=
    inferInstanceAs (CommRing ((smallEtaleRingedSite B (Spec (.of Λ)) hΛ P.space
      P.algebraic).O.obj.obj (op d.U)))
  exact (mul_comm (familyChartScalar B hΛ hSpec P d.U εA) c).trans hc

include hann in
/-- **Multiplication by `ε` is a cokernel of the inclusion of the ideal of the special fibre.** -/
def isColimitSpecialEpsilonMul :
    IsColimit (CokernelCofork.ofπ (specialEpsilonMul B hΛ hSpec P f εA hk)
      (definingIdealSheaf_ι_comp_specialEpsilonMul B hΛ hSpec P f εA hk hG)) :=
  haveI := epi_specialEpsilonMul B hΛ hSpec P f εA hk
  Abelian.epiIsCokernelOfKernel _ (isLimitSpecialEpsilonMul B hΛ hSpec P f εA hk hann hG)

include hann in
/-- **The conormal module of the special fibre of a flat family over an object with a
dual-number coordinate is free of rank one**: `𝒞_{G/X'} ≅ 𝒪_G`. -/
def spaceSpecialConormalIsoUnit :
    conormalModule B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
        (spaceSpecialSubspace B hΛ hSpec P f) ≅
      SheafOfModules.unit (structureRingSheaf B (Spec (.of Λ)) hΛ
        (⟨(spaceSpecialSubspace B hΛ hSpec P f).1.toFunctor,
          (spaceSpecialSubspace B hΛ hSpec P f).2.1⟩ : AlgebraicSpaces B (Spec (.of Λ)) hΛ)) :=
  conormalModuleIsoUnitOfIsColimit B (Spec (.of Λ)) hΛ _ _
    (isColimitSpecialEpsilonMul B hΛ hSpec P f εA hk hann hG)

end Epsilon

end Deformation.Examples

end
