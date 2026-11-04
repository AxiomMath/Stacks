module

public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import StacksFrontier.CategoryTheory.KanExtension.ExtendExactness
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentQuasicoherentClosure

/-!
# Extending right exact tensor functors from coherent to quasi-coherent modules

Stacks 0GRJ: let `𝒳` and `𝒴` be Noetherian algebraic stacks. Any right exact tensor functor
`F : Coh(𝒪_𝒳) ⟶ Coh(𝒪_𝒴)` extends uniquely to a right exact tensor functor
`F : QCoh(𝒪_𝒳) ⟶ QCoh(𝒪_𝒴)` commuting with all colimits.

The source's proof applies Stacks 0FWY to `Coh(𝒪_𝒳) ⊆ QCoh(𝒪_𝒳)`, using that coherent modules
are categorically compact (Stacks 0GQZ) and that every quasi-coherent module is a filtered
colimit of coherent ones (Stacks 0GRF). This file states the result over the second of those
two inputs, in the weak form in which 0FWY consumes it: every quasi-coherent module is a
filtered colimit of coherent modules, `(coherentQuasicoherent B S hS 𝒳).ind`. Everything else the
proof uses is proved: compactness in
`AlgebraicGeometry.Stack.coherentQuasicoherent_le_isFinitelyPresentable`, the closure of `Coh`
under finite colimits and tensor products and the commutation of tensor products with colimits
in `StacksFrontier.AlgebraicGeometry.Stacks.CoherentQuasicoherentClosure`, and the categorical
argument in `CategoryTheory.ObjectProperty.existsUnique_tensorExtension`.

## Main definitions

* `CategoryTheory.Functor.TensorStructure.compι`: a functor of monoidal categories (Stacks 0FFL)
  into a full monoidal subcategory stays one after composing with the inclusion.

## Main results

* `AlgebraicGeometry.Stack.existsUnique_tensorExtension_quasicoherent_of_coherentGeneration`:
  the extension of a functor `Coh(𝒪_𝒳) ⟶ QCoh(𝒪_𝒴)`.
* `AlgebraicGeometry.Stack.existsUnique_tensorExtension_of_coherentGeneration`: **Stacks 0GRJ,
  over the generation of `QCoh(𝒪_𝒳)` by `Coh(𝒪_𝒳)` under filtered colimits** (Stacks 0GRF).

## Implementation notes

"Right exact" is read as preservation of finite colimits together with additivity, which is how
the source uses it (its proof notes that the extension is additive). A "tensor functor" is a
functor of monoidal categories in the sense of Stacks 0FFL,
`CategoryTheory.Functor.TensorStructure`. Uniqueness is uniqueness up to unique isomorphism
compatible with the identification on coherent modules, among functors commuting with filtered
colimits, and that isomorphism is compatible with every tensor structure compatible with the one
of `F` on coherent modules.

## References

* [Stacks Project, Tag 0GRJ](https://stacks.math.columbia.edu/tag/0GRJ)
* [Stacks Project, Tag 0FWY](https://stacks.math.columbia.edu/tag/0FWY)
* [Stacks Project, Tag 0GRF](https://stacks.math.columbia.edu/tag/0GRF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u w w' v v' u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v'} D]
  [MonoidalCategory C] [MonoidalCategory D] (Q : ObjectProperty D) [Q.IsMonoidal]

/-- A functor of monoidal categories (Stacks 0FFL) into a full monoidal subcategory remains one
after composing with the inclusion: the inclusion is strict monoidal. -/
def TensorStructure.compι {F : C ⥤ Q.FullSubcategory} (hF : F.TensorStructure) :
    (F ⋙ Q.ι).TensorStructure where
  μIso X Y := Q.ι.mapIso (hF.μIso X Y)
  μIso_natural_left f Y := congrArg (fun φ ↦ φ.hom) (hF.μIso_natural_left f Y)
  μIso_natural_right X _ _ g := congrArg (fun φ ↦ φ.hom) (hF.μIso_natural_right X g)
  associativity X Y Z := congrArg (fun φ ↦ φ.hom) (hF.associativity X Y Z)
  isUnitObject_obj_tensorUnit := by
    obtain ⟨e⟩ := (isUnitObject_iff _).1 hF.isUnitObject_obj_tensorUnit
    exact (isUnitObject_iff _).2 ⟨Q.ι.mapIso e⟩

end CategoryTheory.Functor

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Instances

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- `QCoh(𝒪_𝒳)` has a zero object: it is preadditive with an initial object. -/
theorem hasZeroObject_quasicoherentModules :
    HasZeroObject (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids) :=
  let := FibredSite.hasColimitsOfSize_quasicoherentModules' B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids
  let : HasColimitsOfSize.{0, 0} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) := hasColimitsOfSizeShrink.{0, 0} _
  have : HasInitial (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) := HasColimitsOfSize.has_colimits_of_shape _
  hasZeroObject_of_hasInitial_object

variable (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
  (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)

include h𝒳

/-- On a locally Noetherian algebraic stack the inclusion `Coh(𝒪_𝒳) ⟶ QCoh(𝒪_𝒳)` is right
exact: `Coh(𝒪_𝒳)` is closed under binary coproducts, the empty colimit and coequalizers. -/
theorem preservesFiniteColimits_coherentQuasicoherentι :
    PreservesFiniteColimits (coherentQuasicoherent B S hS 𝒳).ι := by
  let := FibredSite.hasColimitsOfSize_quasicoherentModules' B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids
  let : HasColimitsOfSize.{0, 0} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) := hasColimitsOfSizeShrink.{0, 0} _
  let P := coherentQuasicoherent B S hS 𝒳
  have := coherentQuasicoherent_isClosedUnderColimitsOfShape_pair B S hS 𝒳 h𝒳
  have := coherentQuasicoherent_isClosedUnderColimitsOfShape_empty B S hS 𝒳 h𝒳
  have := coherentQuasicoherent_isClosedUnderColimitsOfShape_parallelPair B S hS 𝒳 h𝒳
  have hc : ∀ (J : Type) [SmallCategory J], HasColimitsOfShape J
      (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids) := fun J _ ↦ HasColimitsOfSize.has_colimits_of_shape J
  have key : ∀ (J : Type) [SmallCategory J] [P.IsClosedUnderColimitsOfShape J],
      PreservesColimitsOfShape J P.ι := fun J _ _ ↦
    have := hc J
    have : HasColimitsOfShape J P.FullSubcategory := hasColimitsOfShape_of_closedUnderColimits _ P
    @preservesColimitOfShape_of_createsColimitsOfShape_and_hasColimitsOfShape _ _ _ _ _ _ _
      (createsColimitsOfShapeFullSubcategoryInclusion _ P) (hc J)
  have := hc (Discrete WalkingPair)
  have := hc (Discrete PEmpty.{1})
  have : HasColimitsOfShape (Discrete WalkingPair) P.FullSubcategory :=
    hasColimitsOfShape_of_closedUnderColimits _ P
  have : HasColimitsOfShape (Discrete PEmpty.{1}) P.FullSubcategory :=
    hasColimitsOfShape_of_closedUnderColimits _ P
  have := key (Discrete WalkingPair)
  have := key (Discrete PEmpty.{1})
  have := key WalkingParallelPair
  have : HasFiniteCoproducts P.FullSubcategory := hasFiniteCoproducts_of_has_binary_and_initial
  have : PreservesFiniteCoproducts P.ι :=
    ⟨fun _ ↦ PreservesFiniteCoproducts.of_preserves_binary_and_initial _ _⟩
  exact preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts _

end Instances

attribute [local instance] FibredSite.monoidalCategoryQuasicoherentModules

/-- **The extension of a right exact tensor functor out of `Coh(𝒪_𝒳)`, valued in
`QCoh(𝒪_𝒴)`.** Let `𝒳` and `𝒴` be Noetherian algebraic stacks, and assume that every
quasi-coherent `𝒪_𝒳`-module is a filtered colimit of coherent ones (Stacks 0GRF). Every additive
functor `F' : Coh(𝒪_𝒳) ⟶ QCoh(𝒪_𝒴)` preserving finite colimits, with the structure of a functor
of monoidal categories (Stacks 0FFL), extends to a functor `F : QCoh(𝒪_𝒳) ⟶ QCoh(𝒪_𝒴)` which is
additive, preserves finite colimits, commutes with all small colimits and is a functor of
monoidal categories compatibly with `F'`; the extension is unique up to unique isomorphism among
functors commuting with filtered colimits, and that isomorphism respects tensor structures. -/
theorem existsUnique_tensorExtension_quasicoherent_of_coherentGeneration
    (𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS) (h𝒳 : IsNoetherianStack.{u, w, w'} B S hS 𝒳)
    (_h𝒴 : IsNoetherianStack.{u, w, w'} B S hS 𝒴)
    (hgen : ∀ M : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids, (coherentQuasicoherent B S hS 𝒳).ind.{u} M) :
    haveI := coherentQuasicoherent_isMonoidal B S hS 𝒳 h𝒳.2.2
    ∀ (F' : (coherentQuasicoherent B S hS 𝒳).FullSubcategory ⥤
        FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒴.val.val.p
          𝒴.val.isFiberedInGroupoids) [F'.Additive] [PreservesFiniteColimits F']
      (hF' : F'.TensorStructure),
      ∃ (F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids ⥤
          FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒴.val.val.p
            𝒴.val.isFiberedInGroupoids)
        (e : (coherentQuasicoherent B S hS 𝒳).ι ⋙ F ≅ F') (hF : F.TensorStructure),
        (F.Additive ∧ PreservesFiniteColimits F ∧ PreservesColimitsOfSize.{u, u} F ∧
          (hF.restrict (coherentQuasicoherent B S hS 𝒳)).IsCompatible hF' e) ∧
        ∀ (G : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
            𝒳.val.isFiberedInGroupoids ⥤
            FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒴.val.val.p
              𝒴.val.isFiberedInGroupoids),
          PreservesFilteredColimitsOfSize.{u, u} G →
            ∀ (e' : (coherentQuasicoherent B S hS 𝒳).ι ⋙ G ≅ F'),
              ∃! φ : F ≅ G, Functor.whiskerLeft (coherentQuasicoherent B S hS 𝒳).ι φ.hom =
                  (e ≪≫ e'.symm).hom ∧
                ∀ hG : G.TensorStructure,
                  (hG.restrict (coherentQuasicoherent B S hS 𝒳)).IsCompatible hF' e' →
                    hF.IsCompatible hG φ := by
  intro F' _ _ hF'
  have := coherentQuasicoherent_isMonoidal B S hS 𝒳 h𝒳.2.2
  let := FibredSite.hasColimitsOfSize_quasicoherentModules' B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids
  let := FibredSite.hasColimitsOfSize_quasicoherentModules' B S hS 𝒴.val.val.p
    𝒴.val.isFiberedInGroupoids
  have := hasZeroObject_quasicoherentModules B S hS 𝒳
  have := hasZeroObject_quasicoherentModules B S hS 𝒴
  have : HasFiniteColimits (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) := hasFiniteColimits_of_hasColimitsOfSize _
  have : HasFiniteColimits (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
      𝒴.val.val.p 𝒴.val.isFiberedInGroupoids) := hasFiniteColimits_of_hasColimitsOfSize _
  have := coherentQuasicoherent_isClosedUnderColimitsOfShape_pair B S hS 𝒳 h𝒳.2.2
  have := coherentQuasicoherent_isClosedUnderColimitsOfShape_empty B S hS 𝒳 h𝒳.2.2
  have := coherentQuasicoherent_isClosedUnderColimitsOfShape_parallelPair B S hS 𝒳 h𝒳.2.2
  have := fun M ↦ preservesColimitsOfSize_quasicoherentTensorLeft B S hS 𝒳 M
  have := fun M ↦ preservesColimitsOfSize_quasicoherentTensorRight B S hS 𝒳 M
  have := fun M ↦ preservesColimitsOfSize_quasicoherentTensorLeft B S hS 𝒴 M
  have := fun M ↦ preservesColimitsOfSize_quasicoherentTensorRight B S hS 𝒴 M
  exact ObjectProperty.existsUnique_tensorExtension (coherentQuasicoherent B S hS 𝒳)
    (coherentQuasicoherent_le_isFinitelyPresentable B S hS 𝒳 h𝒳) hgen F' hF'

/-- **Stacks 0GRJ, over the generation of `QCoh(𝒪_𝒳)` by coherent modules (Stacks 0GRF).** Let
`𝒳` and `𝒴` be Noetherian algebraic stacks, and assume that every quasi-coherent `𝒪_𝒳`-module
is a filtered colimit of coherent `𝒪_𝒳`-modules. Any right exact tensor functor
`F' : Coh(𝒪_𝒳) ⟶ Coh(𝒪_𝒴)` — additive, preserving finite colimits, and a functor of monoidal
categories (Stacks 0FFL) — extends to a right exact tensor functor
`F : QCoh(𝒪_𝒳) ⟶ QCoh(𝒪_𝒴)` commuting with all colimits: there is an identification `e` of the
restriction of `F` to `Coh(𝒪_𝒳)` with `F'` (followed by the inclusion of `Coh(𝒪_𝒴)`), compatible
with the tensor structures. The extension is unique: for any other functor `G` commuting with
filtered colimits and identification `e'`, there is a unique isomorphism `F ≅ G` restricting to
`e' ⁻¹ ∘ e` on coherent modules, and it is compatible with any tensor structure on `G` for which
`e'` is.

The hypothesis `hgen` is the form in which Stacks 0FWY consumes Stacks 0GRF ("every
quasi-coherent module is a filtered colimit of its coherent submodules"); nothing else is
assumed. -/
theorem existsUnique_tensorExtension_of_coherentGeneration
    (𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS) (h𝒳 : IsNoetherianStack.{u, w, w'} B S hS 𝒳)
    (h𝒴 : IsNoetherianStack.{u, w, w'} B S hS 𝒴)
    (hgen : ∀ M : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids, (coherentQuasicoherent B S hS 𝒳).ind.{u} M) :
    haveI := coherentQuasicoherent_isMonoidal B S hS 𝒳 h𝒳.2.2
    haveI := coherentQuasicoherent_isMonoidal B S hS 𝒴 h𝒴.2.2
    ∀ (F' : (coherentQuasicoherent B S hS 𝒳).FullSubcategory ⥤
        (coherentQuasicoherent B S hS 𝒴).FullSubcategory) [F'.Additive]
      [PreservesFiniteColimits F'] (hF' : F'.TensorStructure),
      ∃ (F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids ⥤
          FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒴.val.val.p
            𝒴.val.isFiberedInGroupoids)
        (e : (coherentQuasicoherent B S hS 𝒳).ι ⋙ F ≅ F' ⋙ (coherentQuasicoherent B S hS 𝒴).ι)
        (hF : F.TensorStructure),
        (F.Additive ∧ PreservesFiniteColimits F ∧ PreservesColimitsOfSize.{u, u} F ∧
          (hF.restrict (coherentQuasicoherent B S hS 𝒳)).IsCompatible
            (hF'.compι (coherentQuasicoherent B S hS 𝒴)) e) ∧
        ∀ (G : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
            𝒳.val.isFiberedInGroupoids ⥤
            FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒴.val.val.p
              𝒴.val.isFiberedInGroupoids),
          PreservesFilteredColimitsOfSize.{u, u} G →
            ∀ (e' : (coherentQuasicoherent B S hS 𝒳).ι ⋙ G ≅
                F' ⋙ (coherentQuasicoherent B S hS 𝒴).ι),
              ∃! φ : F ≅ G, Functor.whiskerLeft (coherentQuasicoherent B S hS 𝒳).ι φ.hom =
                  (e ≪≫ e'.symm).hom ∧
                ∀ hG : G.TensorStructure,
                  (hG.restrict (coherentQuasicoherent B S hS 𝒳)).IsCompatible
                    (hF'.compι (coherentQuasicoherent B S hS 𝒴)) e' →
                    hF.IsCompatible hG φ := by
  intro F' _ _ hF'
  have := coherentQuasicoherent_isMonoidal B S hS 𝒳 h𝒳.2.2
  have := coherentQuasicoherent_isMonoidal B S hS 𝒴 h𝒴.2.2
  have := preservesFiniteColimits_coherentQuasicoherentι B S hS 𝒴 h𝒴.2.2
  have : PreservesFiniteColimits (F' ⋙ (coherentQuasicoherent B S hS 𝒴).ι) :=
    comp_preservesFiniteColimits _ _
  exact existsUnique_tensorExtension_quasicoherent_of_coherentGeneration B S hS 𝒳 𝒴 h𝒳 h𝒴 hgen
    (F' ⋙ (coherentQuasicoherent B S hS 𝒴).ι) (hF'.compι (coherentQuasicoherent B S hS 𝒴))

end AlgebraicGeometry.Stack

end
