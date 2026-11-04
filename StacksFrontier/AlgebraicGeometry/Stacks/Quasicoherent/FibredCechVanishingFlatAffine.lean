module

public import StacksFrontier.AlgebraicGeometry.Limits.Descending.InfiniteProducts
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FibredTensorToSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FibreProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.AmbientTensorPresheafCechVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexAlongAFunctor
public import StacksFrontier.CategoryTheory.Sites.Continuous.CoveringPullbacks
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCechVanishingTensorPresheaf
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationAffine
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Čech vanishing on finite fppf coverings by affine objects of a fibred site

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and `x` an object of `𝒳` lying
over an affine scheme `X`.  Let `{zᵢ ⟶ x}` be a finite family of objects of `𝒳` lying over affine
schemes `Zᵢ`, whose image `{Zᵢ ⟶ X}` is an fppf covering of schemes, and let `P` be an abelian
presheaf on `𝒳` which on the slice `𝒳/x` receives a comparison from the ambient coefficient
presheaf `Γ(-, 𝒪) ⊗_{Γ(X, 𝒪)} M` of a bare module `M`, invertible at every object of the slice
lying over an affine scheme over `X` by a morphism with a property `P` — flat, for the fppf
site; étale, for the étale site — stable under base change and composition.  Then the Čech
cohomology of `P` on `{zᵢ ⟶ x}` vanishes in positive degrees.

This is Stacks 03FJ transported to the fibred site, in the shape of
`AlgebraicGeometry.Space.SmallEtale.isZero_cechCohomology_succ_of_overTensorPresheafIso`: the
family is lifted one slice up, its Čech cohomology is carried down along `Over.forget x` and over
along the functor `𝒳/x ⥤ Sch/X` induced by `p`, which preserves the fibre products because `p`
does (Stacks 06N6), and downstairs it is the Amitsur complex of a faithfully flat ring map.

The objects at which the comparison is evaluated are the iterated fibre products of the family
over `x`; they lie over affine schemes `P` over `X`, by
`AlgebraicGeometry.FibredSite.isAffine_prop_sliceHypercover_piObj`.  That is where the comparison
of a module with the flat base change property (`P` flat), respectively of a locally
quasi-coherent module (`P` étale), is invertible.

## Main results

* `AlgebraicGeometry.prop_over_finiteProduct`: the structure morphism of a finite product of
  schemes over `K` has every property stable under base change and composition which the
  factors have.
* `AlgebraicGeometry.FibredSite.preservesPullbacks_of_isFiberedInGroupoids`: a functor fibred in
  groupoids over the big fppf site preserves fibre products.
* `AlgebraicGeometry.FibredSite.isZero_cechCohomology_succ_of_tensorToSections`: **the Čech
  vanishing.**

## References

* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 06N6](https://stacks.math.columbia.edu/tag/06N6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.CechSite

universe w v u

namespace AlgebraicGeometry

/-- A property respecting isomorphisms of the structure morphism of an object over `K` passes
to every isomorphic object over `K`. -/
private theorem prop_hom_of_overIso (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {K : Scheme.{u}} {Y Z : Over K} (e : Y ≅ Z) (h : P Z.hom) : P Y.hom := by
  have : IsIso e.hom.left := (Over.forget K).map_isIso e.hom
  rw [← Over.w e.hom]
  exact (P.cancel_left_of_respectsIso e.hom.left Z.hom).2 h

/-- **The structure morphism of a finite product over `K` of schemes whose structure morphisms
have a property `P` stable under base change and composition and containing the identities has
`P`.**  Induction on the finite index type, a binary product over `K` being a fibre product. -/
@[ega "I 3.5.1" "(ii) ⇒ (i), special case"]
theorem prop_over_finiteProduct (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.IsStableUnderComposition] [P.ContainsIdentities] {K : Scheme.{u}} {α : Type w} [Finite α]
    (Y : α → Over K) [HasFiniteProducts (Over K)]
    (hY : ∀ a, P (Y a).hom) : P (∏ᶜ Y).hom := by
  classical
  have := Fintype.ofFinite α
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine Fintype.induction_empty_option
    (P := fun α _ => ∀ (Y : α → Over K), (∀ a, P (Y a).hom) →
      P (∏ᶜ Y).hom) ?_ ?_ ?_ α Y hY
  · intro α β _ e ih Z hZ
    have : HasProduct (fun a : α => Z (e a)) :=
      hasProduct_of_equiv_of_iso Z (fun a => Z (e a)) e (fun _ => Iso.refl _)
    exact prop_hom_of_overIso P (Pi.whiskerEquiv e fun _ => Iso.refl _).symm
      (ih (fun a : α => Z (e a)) fun a => hZ (e a))
  · intro Y hY
    have hP : IsTerminal (∏ᶜ Y) := IsTerminal.ofUniqueHom
      (fun X => Pi.lift fun a => isEmptyElim a)
      (fun _ _ => Pi.hom_ext _ _ fun a => isEmptyElim a)
    exact prop_hom_of_overIso P (hP.uniqueUpToIso Over.mkIdTerminal) (P.id_mem K)
  · intro α _ ih Y hY
    let R : Over K := ∏ᶜ (fun a : α => Y (some a))
    have hB : P (Y none ⨯ R).hom := by
      have hEq : (Over.prodLeftIsoPullback (Y none) R).hom ≫
          (Limits.pullback.fst (Y none).hom R.hom ≫ (Y none).hom) = (Y none ⨯ R).hom := by
        rw [← Category.assoc, Over.prodLeftIsoPullback_hom_fst]
        exact (prod.fst (X := Y none) (Y := R)).w
      rw [← hEq]
      exact P.comp_mem _ _ (P.of_isIso _) <| P.comp_mem _ _
        (P.pullback_fst _ _ (ih (fun a : α => Y (some a)) fun a => hY (some a))) (hY none)
    exact prop_hom_of_overIso P (overOptionProductIso (K := K) (α := α) Y) hB

namespace FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

include hp in
/-- **A functor fibred in groupoids over the big fppf site preserves fibre products**: it
carries a pullback square of the source to a pullback square of the target (Stacks 06N6 (2)). -/
theorem preservesPullbacks_of_isFiberedInGroupoids : PreservesLimitsOfShape WalkingCospan p := by
  have := BigFppfOver.hasPullbacks_of_isFiberedInGroupoids B S hS p hp
  refine ⟨fun {K} => ?_⟩
  have key : ∀ {X Y Z : 𝒳} (g : X ⟶ Z) (h : Y ⟶ Z), PreservesLimit (cospan g h) p := by
    intro X Y Z g h
    have hX : IsPullback (pullback.fst g h) (pullback.snd g h) g h :=
      IsPullback.of_hasPullback g h
    exact preservesLimit_of_preserves_limit_cone hX.isLimit
      ((isLimitMapConePullbackConeEquiv p hX.w).symm (hp.map_isPullback p g h _ _ hX).isLimit)
  have := key (K.map WalkingCospan.Hom.inl) (K.map WalkingCospan.Hom.inr)
  exact preservesLimit_of_iso_diagram _ (diagramIsoCospan K).symm

variable {B S hS p} in
/-- A family of morphisms of `𝒳` with target `x`, read as a family in the slice `𝒳/x` with
target the terminal object `Over.mk (𝟙 x)`. -/
def sliceHypercover {x : 𝒳} (E : PreZeroHypercover.{u} x) :
    PreZeroHypercover.{u} (Over.mk (𝟙 x)) where
  I₀ := E.I₀
  X i := Over.mk (E.f i)
  f i := Over.homMk (E.f i) (by simp)

/-- Pushing `sliceHypercover E` forward along the forgetful functor `Over x ⥤ 𝒳` recovers the
family `E`. -/
theorem sliceHypercover_map_forget {x : 𝒳} (E : PreZeroHypercover.{u} x) :
    (sliceHypercover E).map (Over.forget x) = E := rfl

include hp in
/-- **An iterated fibre product, in the slice at `x`, of a family of objects lying over affine
schemes `P` over the affine scheme below `x`, lies over an affine scheme `P` over it**, for `P`
stable under base change and composition and containing the identities. -/
theorem isAffine_prop_sliceHypercover_piObj (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsStableUnderComposition] [P.ContainsIdentities]
    {x : 𝒳} (hx : IsAffine (schemeOf B S hS p x))
    (E : PreZeroHypercover.{u} x) (haff : ∀ i, IsAffine (schemeOf B S hS p (E.X i)))
    (hflat : ∀ i, P ((p ⋙ BigFppfOver.toScheme B S hS).map (E.f i)))
    (n : ℕ) (i : Fin (n + 1) → E.I₀) :
    letI : HasPullbacks 𝒳 := BigFppfOver.hasPullbacks_of_isFiberedInGroupoids B S hS p hp
    letI : HasFiniteLimits (Over x) := hasFiniteLimits_of_hasTerminal_and_pullbacks
    letI : HasFiniteLimits (Over (Over.mk (𝟙 x))) :=
      hasFiniteLimits_of_hasTerminal_and_pullbacks
    IsAffine (schemeOf B S hS p
        (∏ᶜ (fun a ↦ Over.mk ((sliceHypercover E).f (i a)))).left.left) ∧
      P ((sliceToSchemes B S hS p x).obj
        (∏ᶜ (fun a ↦ Over.mk ((sliceHypercover E).f (i a)))).left).hom := by
  have : HasPullbacks 𝒳 := BigFppfOver.hasPullbacks_of_isFiberedInGroupoids B S hS p hp
  have : HasFiniteLimits (Over x) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  have : HasFiniteLimits (Over (Over.mk (𝟙 x))) :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  have := preservesPullbacks_of_isFiberedInGroupoids B S hS p hp
  let v : Over x ⥤ Scheme.{u} := Over.forget x ⋙ p ⋙ BigFppfOver.toScheme B S hS
  let A : Fin (n + 1) → Over (Over.mk (𝟙 x)) := fun a ↦ Over.mk ((sliceHypercover E).f (i a))
  have : IsAffine (v.obj (Over.mk (𝟙 x))) := hx
  have : PreservesLimit (Discrete.functor A) (Over.post (X := Over.mk (𝟙 x)) v) :=
    Stacks.Sites.preservesLimit_fibreProducts_overPost v (sliceHypercover E)
      (fun _ _ _ ↦ inferInstance) (fun _ _ _ ↦ inferInstance) n i
  have haffhom : ∀ a, IsAffineHom ((Over.post (X := Over.mk (𝟙 x)) v).obj (A a)).hom :=
    fun a ↦ by
      have : IsAffine ((Over.post (X := Over.mk (𝟙 x)) v).obj (A a)).left := haff (i a)
      exact isAffineHom_of_isAffine _
  have : IsAffineHom (∏ᶜ (fun a ↦ (Over.post (X := Over.mk (𝟙 x)) v).obj (A a))).hom :=
    isAffineHom_over_finiteProduct _ haffhom
  have : IsAffine (∏ᶜ (fun a ↦ (Over.post (X := Over.mk (𝟙 x)) v).obj (A a))).left :=
    isAffine_of_isAffineHom (∏ᶜ (fun a ↦ (Over.post (X := Over.mk (𝟙 x)) v).obj (A a))).hom
  let e : (Over.post (X := Over.mk (𝟙 x)) v).obj (∏ᶜ A) ≅
      ∏ᶜ (fun a ↦ (Over.post (X := Over.mk (𝟙 x)) v).obj (A a)) :=
    PreservesProduct.iso (Over.post (X := Over.mk (𝟙 x)) v) A
  refine ⟨?_, ?_⟩
  · have e' : schemeOf B S hS p (∏ᶜ A).left.left ≅
        (∏ᶜ (fun a ↦ (Over.post (X := Over.mk (𝟙 x)) v).obj (A a))).left :=
      (Over.forget (v.obj (Over.mk (𝟙 x)))).mapIso e
    exact IsAffine.of_isIso e'.hom
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  change P ((p ⋙ BigFppfOver.toScheme B S hS).map (∏ᶜ A).left.hom)
  rw [← show (∏ᶜ A).hom.left = (∏ᶜ A).left.hom by simpa using Over.w (∏ᶜ A).hom]
  exact prop_hom_of_overIso P e (prop_over_finiteProduct P _ fun a ↦ hflat (i a))

/-- A functor preserving pullbacks has invertible comparison maps for the iterated fibre products
of any family over an object of a category with pullbacks. -/
private theorem isIso_cechProductMapOfFunctor_of_preservesPullbacks {C : Type*} [Category* C]
    {D : Type*} [Category* D] [HasPullbacks C] (u : C ⥤ D) [PreservesLimitsOfShape WalkingCospan u]
    {X : C} (E : PreZeroHypercover.{u} X)
    [hE : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    [hEu : ∀ (n : ℕ) (i : Fin (n + 1) → (E.map u).I₀),
      HasProduct (fun a ↦ Over.mk ((E.map u).f (i a)))]
    (n : ℕ) (i : Fin (n + 1) → E.I₀) : IsIso (cechProductMapOfFunctor u E n i) := by
  have := Stacks.Sites.preservesLimit_fibreProducts_overPost u E
    (fun _ _ _ ↦ inferInstance) (fun _ _ _ ↦ inferInstance) n i
  exact isIso_cechProductMapOfFunctor u E n i

include hp in
/-- **Čech vanishing on a finite fppf covering by affine objects of an object of `𝒳` lying over an
affine scheme**, for an abelian presheaf identified on the slice at `x`, at the objects lying over
affine schemes `P` over `X`, with the ambient coefficient presheaf `Γ(-, 𝒪) ⊗_{Γ(X, 𝒪)} M` of a
bare module.

The family is lifted one slice up by `AlgebraicGeometry.FibredSite.sliceHypercover`; its Čech
cohomology is carried down along `Over.forget x` and over along
`AlgebraicGeometry.FibredSite.sliceToSchemes`, both of which preserve its fibre products, and the
vanishing downstairs is `AlgebraicGeometry.isZero_cechCohomology_succ_overTensorPresheaf`
(Stacks 03FJ) for the standard fppf covering of affine schemes underlying the family. -/
theorem isZero_cechCohomology_succ_of_tensorToSections (Pm : MorphismProperty Scheme.{u})
    [Pm.IsStableUnderBaseChange] [Pm.IsStableUnderComposition] [Pm.ContainsIdentities] {x : 𝒳}
    (hx : IsAffine (schemeOf B S hS p x))
    (E : PreZeroHypercover.{u} x) (hfin : Finite E.I₀)
    (haff : ∀ i, IsAffine (schemeOf B S hS p (E.X i)))
    (hfppf : Presieve.ofArrows (fun i => schemeOf B S hS p (E.X i))
        (fun i => (p ⋙ BigFppfOver.toScheme B S hS).map (E.f i)) ∈
      Scheme.fppfPrecoverage (schemeOf B S hS p x))
    (hP : ∀ i, Pm ((p ⋙ BigFppfOver.toScheme B S hS).map (E.f i)))
    (M : Type u) [AddCommGroup M] [Module (Scheme.Γ.obj (op (schemeOf B S hS p x)) : Type u) M]
    (P : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{u})
    (τ : (sliceToSchemes B S hS p x).op ⋙ overTensorPresheaf (schemeOf B S hS p x) M ⟶
      (Over.forget x).op ⋙ P)
    (hτ : ∀ Z : Over x, IsAffine (schemeOf B S hS p Z.left) →
      Pm ((sliceToSchemes B S hS p x).obj Z).hom → IsIso (τ.app (op Z)))
    (n : ℕ) (hn : 0 < n) :
    letI : HasPullbacks 𝒳 := BigFppfOver.hasPullbacks_of_isFiberedInGroupoids B S hS p hp
    letI : HasFiniteLimits (Over x) := hasFiniteLimits_of_hasTerminal_and_pullbacks
    IsZero (cechCohomology E P n) := by
  have : HasPullbacks 𝒳 := BigFppfOver.hasPullbacks_of_isFiberedInGroupoids B S hS p hp
  have : HasFiniteLimits (Over x) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  have : HasFiniteLimits (Over (Over.mk (𝟙 x))) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  have := preservesPullbacks_of_isFiberedInGroupoids B S hS p hp
  have : IsAffine ((sliceToSchemes B S hS p x).obj (Over.mk (𝟙 x))).left := hx
  have : HasFiniteLimits (Over ((sliceToSchemes B S hS p x).obj (Over.mk (𝟙 x)))) :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  have hpx : ∀ (n : ℕ)
      (i : Fin (n + 1) → ((sliceHypercover E).map (Over.forget x)).I₀),
      HasProduct (fun a ↦ Over.mk (((sliceHypercover E).map (Over.forget x)).f (i a))) :=
    fun n i ↦ (inferInstance : HasProduct (fun a ↦ Over.mk (E.f (i a))))
  have hstd : IsStandardCovering .fppf
      (fun i ↦ (((sliceHypercover E).map (sliceToSchemes B S hS p x)).X i).left)
      (fun i ↦ (((sliceHypercover E).map (sliceToSchemes B S hS p x)).f i).left) := by
    unfold Scheme.fppfPrecoverage at hfppf
    obtain ⟨hsurj, hfl⟩ := (Scheme.ofArrows_mem_precoverage_iff _).1 hfppf
    refine ⟨hfin, haff, Set.eq_univ_of_forall fun t ↦ Set.mem_iUnion.2 (hsurj t), fun i ↦
      ⟨(hfl i).1, @finitePresentation_of_isAffine _ _
        ((p ⋙ BigFppfOver.toScheme B S hS).map (E.f i)) (haff i) hx (hfl i).2⟩⟩
  have hg : ((sliceToSchemes B S hS p x).obj (Over.mk (𝟙 x))).hom = 𝟙 _ :=
    (p ⋙ BigFppfOver.toScheme B S hS).map_id x
  have hslicezero : IsZero (cechCohomology (sliceHypercover E)
      ((sliceToSchemes B S hS p x).op ⋙ overTensorPresheaf (schemeOf B S hS p x) M) n) :=
    (isZero_cechCohomology_succ_overTensorPresheaf (schemeOf B S hS p x) M hg .fppf
      ((sliceHypercover E).map (sliceToSchemes B S hS p x)) hstd n hn).of_iso
      (cechCohomologyIsoOfFunctor (sliceToSchemes B S hS p x) (sliceHypercover E)
        (overTensorPresheaf (schemeOf B S hS p x) M)
        (fun _ _ ↦ isIso_cechProductMapOfFunctor_of_preservesPullbacks _ _ _ _) n).symm
  have hτiso : IsIso ((Stacks.CechSite.cechComplexFunctor (sliceHypercover E)).map τ) :=
    isIso_cechComplexFunctor_map (sliceHypercover E) τ fun n i ↦
      (isAffine_prop_sliceHypercover_piObj B S hS p hp Pm hx E haff hP n i).elim (hτ _)
  have hcoeff : IsZero (cechCohomology (sliceHypercover E) ((Over.forget x).op ⋙ P) n) :=
    hslicezero.of_iso
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) n).mapIso
        (asIso ((Stacks.CechSite.cechComplexFunctor (sliceHypercover E)).map τ))).symm
  exact hcoeff.of_iso (cechCohomologyIsoOfFunctor (Over.forget x) (sliceHypercover E) P
    (fun _ _ ↦ isIso_cechProductMapOfFunctor_of_preservesPullbacks _ _ _ _) n)

end FibredSite

end AlgebraicGeometry
