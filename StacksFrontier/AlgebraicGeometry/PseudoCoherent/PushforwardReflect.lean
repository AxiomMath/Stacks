module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPushforwardPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FiniteTypeDegreeZero
public import StacksFrontier.Topology.OpensMapFinal

/-!
# What `i_*` reflects at a closed immersion of ringed spaces

Let `i : Z ⟶ X` be a morphism of ringed spaces. The forward half of Stacks 09VA uses only that
`i_*` is exact; its converse half uses, in addition, that `i_*` *reflects* information, and this
file collects the three reflections the converse needs together with the adjunction step that
feeds them.

Everything rests on one observation: when the underlying continuous map of `i` is inducing, every
open of `Z` is the preimage of an open of `X`
(`AlgebraicGeometry.RingedSpace.exists_opens_preimage_eq`), and the sections of `i_*F` over an
open `U` of `X` are the sections of `F` over `i⁻¹U`. So `i_*F = 0` forces `F = 0`; exactness then
turns that into reflection of epimorphisms, by way of cokernels.

The adjunction `i^* ⊣ i_*` turns an epimorphism `𝒪_X^{⊕n} ⟶ i_*𝒢` into an epimorphism
`𝒪_Z^{⊕n} ⟶ 𝒢`, because `i^*𝒪_X = 𝒪_Z` and because the unit of the adjunction splits off the
first factor of the triangle identity. Combined with the reflection of epimorphisms and with the
base-change square `AlgebraicGeometry.RingedSpace.restrictPushforwardIso` this gives that `𝒢` is
of finite type as soon as `i_*𝒢` is, which is the step by which the converse half of Stacks 09VA
reads Stacks 08DN(1) on `X` as a statement about `Z`.

## Main definitions

* `AlgebraicGeometry.RingedSpace.pullbackOXModStructureModuleIso`: `i^*𝒪_X ≅ 𝒪_Z`.
* `AlgebraicGeometry.RingedSpace.pullbackOXModFiniteFreeIso`: `i^*(𝒪_X^{⊕n}) ≅ 𝒪_Z^{⊕n}`.
* `AlgebraicGeometry.RingedSpace.homologyPushforwardComplexIso`: `H^j(i_*𝒦) ≅ i_*H^j(𝒦)` for a
  complex `𝒦` of `𝒪_Z`-modules.
* `AlgebraicGeometry.RingedSpace.homologyDerivedPushforwardOXModIso`: `H^j(Ri_*E) ≅ i_*H^j(E)` for
  an object `E` of `D(𝒪_Z)`.

## Main results

* `AlgebraicGeometry.RingedSpace.subsingleton_sections_of_isZero`: a zero `𝒪`-module has trivial
  sections over every open. This is the converse of
  `AlgebraicGeometry.RingedSpace.isZero_of_subsingleton_sections`.
* `AlgebraicGeometry.RingedSpace.isZero_of_isZero_pushforwardOXMod`: `i_*` reflects zero objects.
* `AlgebraicGeometry.RingedSpace.epi_of_epi_map_pushforwardOXMod`: `i_*` reflects epimorphisms.
* `AlgebraicGeometry.RingedSpace.final_opensMap`: the inverse-image functor on opens is final,
  which is what makes `i^*𝒪_X ≅ 𝒪_Z`.
* `AlgebraicGeometry.RingedSpace.exists_epi_finiteFree_of_epi_pushforward`: an epimorphism
  `𝒪_X^{⊕n} ⟶ i_*𝒢` yields an epimorphism `𝒪_Z^{⊕n} ⟶ 𝒢`.
* `AlgebraicGeometry.RingedSpace.isFiniteType_of_isFiniteType_pushforward`: an `𝒪_Z`-module is of
  finite type as soon as its pushforward is.
* `AlgebraicGeometry.RingedSpace.isZero_homology_of_isZero_homology_derivedPushforward`: the
  cohomology of `E` vanishes in a degree where the cohomology of `Ri_*E` does. This is the
  reduction "after shrinking `X` we may assume `i_*E`, and hence `E`, is bounded above" of the
  converse half of Stacks 09VA, in the direction that reads a bound on `Ri_*E` as a bound on `E`.
* `AlgebraicGeometry.RingedSpace.isFiniteType_homology_of_isPseudoCoherentFrom_derivedPushforward`:
  if `Ri_*E` is `m`-pseudo-coherent and `E` has no cohomology above some `p ≥ m`, then `H^p(E)` is
  an `𝒪_Z`-module of finite type. This is Stacks 08DN(1), read through `i_*`, as the converse half
  of Stacks 09VA uses it.

## Implementation notes

`AlgebraicGeometry.RingedSpace.final_opensMap` is proved rather than taken from Mathlib: the
category `StructuredArrow U (Opens.map i)` of opens `V` of `X` with `U ≤ i⁻¹V` is nonempty,
because `V = ⊤` qualifies, and every object maps to that one, so it is connected. Mathlib's
`SheafOfModules.pullbackObjUnitToUnit` is then an isomorphism, which is `i^*𝒪_X ≅ 𝒪_Z`.

The two instance arguments that Mathlib's pullback API needs — finality and the right-adjointness
of `i_*` — are supplied as terms and the isomorphism is formed with an explicit `@asIso`: an
anonymous `have : IsIso …` in this area is not found by instance search.

`AlgebraicGeometry.RingedSpace.homologyPushforwardComplexIso` is the isomorphism underlying the
already proved `AlgebraicGeometry.RingedSpace.isZero_homology_pushforwardComplex`, which only
needed its existence in order to transport a vanishing statement; the converse half of Stacks 09VA
needs the isomorphism itself, to transport finite generation.

## References

* [Stacks Project, Lemma 20.49.2 (Tag 09VA)](https://stacks.math.columbia.edu/tag/09VA)
* [Stacks Project, Lemma 20.47.4 (Tag 08DN)](https://stacks.math.columbia.edu/tag/08DN)
* [Stacks Project, Lemma 17.6.1 (Tag 01AX)](https://stacks.math.columbia.edu/tag/01AX)
* [Stacks Project, Lemma 6.26.1 (Tag 0096)](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace StrictlyPerfect

universe d u

namespace AlgebraicGeometry.RingedSpace

/-! ### Zero objects and their sections -/

/-- **A zero `𝒪_Y`-module has trivial sections over every open.** Its identity morphism is the
zero morphism, and the identity acts on sections as the identity.

This is the converse of `AlgebraicGeometry.RingedSpace.isZero_of_subsingleton_sections`. -/
public theorem subsingleton_sections_of_isZero {Y : RingedSpace.{u, u}} {M : OXMod.{u, u} Y}
    (h : IsZero M) (W : (Opens Y.carrier)ᵒᵖ) : Subsingleton (M.val.obj W) := by
  rw [IsZero.iff_id_eq_zero] at h
  have hv : (0 : M ⟶ M).val = 0 := rfl
  have key : ∀ a : M.val.obj W, a = 0 := fun a => by
    have h' := congrArg (fun f : M ⟶ M => f.val.app W a) h
    rw [hv] at h'
    simpa using h'
  exact ⟨fun a b => (key a).trans (key b).symm⟩

variable {Z X : RingedSpace.{u, u}} (i : Z ⟶ X)

/-! ### `i_*` reflects zero objects and epimorphisms -/

/-- **`i_*` reflects zero objects** when the underlying continuous map of `i` is inducing.

The sections of `i_*F` over an open `U` of `X` are the sections of `F` over `i⁻¹U`, and every open
of `Z` is of that form (`AlgebraicGeometry.RingedSpace.exists_opens_preimage_eq`), so all the
modules of sections of `F` are trivial. -/
public theorem isZero_of_isZero_pushforwardOXMod (hi : Topology.IsInducing i.hom.base)
    {F : OXMod.{u, u} Z} (h : IsZero ((pushforwardOXMod i).obj F)) : IsZero F := by
  refine isZero_of_subsingleton_sections F fun W => ?_
  obtain ⟨U, hU⟩ := exists_opens_preimage_eq i hi W.unop
  have hW : W = op ((Opens.map i.hom.base).obj U) := by rw [hU]
  rw [hW]
  exact subsingleton_sections_of_isZero h (op U)

/-- **`i_*` reflects epimorphisms** at a closed embedding: if `i_*f` is an epimorphism then so
is `f`.

`i_*` is right exact (Stacks 01AX), so it carries the cokernel of `f` to the cokernel of `i_*f`,
which vanishes; being a closed embedding it also reflects zero objects, so the cokernel of `f`
vanishes and `f` is an epimorphism. -/
public theorem epi_of_epi_map_pushforwardOXMod (hi : Topology.IsClosedEmbedding i.hom.base)
    {A B : OXMod.{u, u} Z} (f : A ⟶ B) (h : Epi ((pushforwardOXMod i).map f)) : Epi f := by
  have := preservesFiniteColimits_pushforwardOXMod i hi
  have := h
  refine Preadditive.epi_of_isZero_cokernel f
    (isZero_of_isZero_pushforwardOXMod i hi.toIsInducing ?_)
  exact IsZero.of_iso (isZero_cokernel_of_epi ((pushforwardOXMod i).map f))
    (PreservesCokernel.iso (pushforwardOXMod i) f)

/-! ### `i^*𝒪_X = 𝒪_Z` -/

/-- **The inverse-image functor on opens is final.** For an open `U` of `Z` the category of opens
`V` of `X` with `U ≤ i⁻¹V` is nonempty, because `V = ⊤` qualifies, and every object of it admits a
morphism to that one, so it is connected.

This is the hypothesis of Mathlib's `SheafOfModules.pullbackObjUnitToUnit` being an isomorphism,
i.e. of `i^*𝒪_X ≅ 𝒪_Z`. -/
public theorem final_opensMap : (Opens.map i.hom.base).Final :=
  Stacks.Topology.final_opensMap i.hom.base

/-- **`i^*𝒪_X ≅ 𝒪_Z`.** Mathlib's comparison `SheafOfModules.pullbackObjUnitToUnit` is an
isomorphism because `AlgebraicGeometry.RingedSpace.final_opensMap` holds. -/
public def pullbackOXModStructureModuleIso :
    (pullbackOXMod i).obj (structureModule X) ≅ structureModule Z := by
  have hfin := final_opensMap i
  have hra : (SheafOfModules.pushforward
      (RingedSpaceModuleAdjunction.structureSheafHom i)).IsRightAdjoint :=
    RingedSpaceModuleAdjunction.modulePushforward_isRightAdjoint i
  exact @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit
      (RingedSpaceModuleAdjunction.structureSheafHom i))
    (SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal _)

/-- **`i^*(𝒪_X^{⊕n}) ≅ 𝒪_Z^{⊕n}`.** The pullback is a left adjoint of the additive functor `i_*`,
hence additive, so it carries the `n`-fold biproduct of `𝒪_X` to the `n`-fold biproduct of
`i^*𝒪_X ≅ 𝒪_Z`. -/
public def pullbackOXModFiniteFreeIso (n : ℕ) :
    (pullbackOXMod i).obj (finiteFree X n) ≅ finiteFree Z n :=
  have := (pullbackPushforwardAdjunctionOXMod i).left_adjoint_additive
  Functor.mapBiproduct (pullbackOXMod i) (fun _ : Fin n => structureModule X) ≪≫
    biproduct.mapIso (fun _ => pullbackOXModStructureModuleIso i)

/-! ### Finite generation descends through `i_*` -/

/-- **An epimorphism `𝒪_X^{⊕n} ⟶ i_*𝒢` yields an epimorphism `𝒪_Z^{⊕n} ⟶ 𝒢`.** This is the
adjunction step of the converse half of Stacks 09VA: "by adjunction we find a map
`𝒪_Z^{⊕n}[-p] ⟶ ℰ^•` which induces a surjection `𝒪_Z^{⊕n} ⟶ H^p(ℰ^•)`".

The adjoint `l : i^*(𝒪_X^{⊕n}) ⟶ 𝒢` of the given map `q` satisfies `q = η ≫ i_*l` for the unit
`η` of `i^* ⊣ i_*`, so `i_*l` is an epimorphism, hence so is `l` because `i_*` reflects
epimorphisms; precomposing with `𝒪_Z^{⊕n} ≅ i^*(𝒪_X^{⊕n})` gives the map asked for. -/
public theorem exists_epi_finiteFree_of_epi_pushforward
    (hi : Topology.IsClosedEmbedding i.hom.base) {G : OXMod.{u, u} Z} {n : ℕ}
    (q : finiteFree X n ⟶ (pushforwardOXMod i).obj G) (hq : Epi q) :
    ∃ q' : finiteFree Z n ⟶ G, Epi q' := by
  set adj := pullbackPushforwardAdjunctionOXMod i with hadj
  set l := (adj.homEquiv (finiteFree X n) G).symm q with hl
  have h1 : adj.homEquiv (finiteFree X n) G l = q := Equiv.apply_symm_apply _ _
  have h2 : adj.homEquiv (finiteFree X n) G l =
      adj.unit.app (finiteFree X n) ≫ (pushforwardOXMod i).map l := adj.homEquiv_unit _ _ _
  have hqeq : adj.unit.app (finiteFree X n) ≫ (pushforwardOXMod i).map l = q := h2.symm.trans h1
  have := hq
  have hmap : Epi ((pushforwardOXMod i).map l) := by
    rw [← hqeq] at hq
    exact epi_of_epi (adj.unit.app (finiteFree X n)) _
  have hlepi : Epi l := epi_of_epi_map_pushforwardOXMod i hi l hmap
  exact ⟨(pullbackOXModFiniteFreeIso i n).inv ≫ l, epi_comp _ _⟩

/-- **An `𝒪_Z`-module is of finite type as soon as its pushforward is**, at a closed embedding.

Finite type is a local condition on `Z`. Near the image `i(z)` of a point of `Z` the module
`i_*F` is a quotient of a finite free module
(`AlgebraicGeometry.RingedSpace.exists_epi_finiteFree_of_isFiniteType`), say on the open `U` of
`X`; the base-change square `AlgebraicGeometry.RingedSpace.restrictPushforwardIso` identifies
`(i_*F)|_U` with `(i|_{i⁻¹U})_*(F|_{i⁻¹U})`, and
`AlgebraicGeometry.RingedSpace.exists_epi_finiteFree_of_epi_pushforward` for the restricted
morphism makes `F|_{i⁻¹U}` a quotient of a finite free module. -/
public theorem isFiniteType_of_isFiniteType_pushforward
    (hi : Topology.IsClosedEmbedding i.hom.base) (F : OXMod.{u, u} Z)
    (h : SheafOfModules.IsFiniteType (R := structureSheafOfRings X)
      ((pushforwardOXMod i).obj F)) :
    SheafOfModules.IsFiniteType (R := structureSheafOfRings Z) F := by
  refine isFiniteType_of_exists_local_free_epi F fun z => ?_
  obtain ⟨U, hzU, n, q, hq⟩ := exists_epi_finiteFree_of_isFiniteType
    ((pushforwardOXMod i).obj F) h (i.hom.base z)
  have hq' : Epi (q ≫ ((restrictPushforwardIso i U).app F).hom) := epi_comp _ _
  obtain ⟨q', hq'epi⟩ := exists_epi_finiteFree_of_epi_pushforward (restrictHom i U)
    (isClosedEmbedding_restrictHom i U hi) (q ≫ ((restrictPushforwardIso i U).app F).hom) hq'
  exact ⟨(Opens.map i.hom.base).obj U, n, hzU,
    exists_epi_free_over_of_epi_finiteFree F ((Opens.map i.hom.base).obj U) n q' hq'epi⟩

/-! ### Cohomology commutes with `i_*` -/

/-- **`H^j(i_*𝒦) ≅ i_*H^j(𝒦)`.** At a closed embedding `i_*` is exact, so it commutes with the
formation of the homology of the degree-`j` short complex of `𝒦`.

This is the isomorphism underlying
`AlgebraicGeometry.RingedSpace.isZero_homology_pushforwardComplex`. -/
public def homologyPushforwardComplexIso (hi : Topology.IsClosedEmbedding i.hom.base)
    (K : CochainComplex (OXMod.{u, u} Z) ℤ) (j : ℤ) :
    (((pushforwardOXMod i).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology j ≅
      (pushforwardOXMod i).obj (K.homology j) :=
  have := preservesFiniteColimits_pushforwardOXMod i hi
  (K.sc j).mapHomologyIso (pushforwardOXMod i)

section Derived

variable [HasDerivedCategory.{d} (OXMod.{u, u} Z)] [HasDerivedCategory.{d} (OXMod.{u, u} X)]

/-- **`H^j(Ri_*E) ≅ i_*H^j(E)`**, the sentence "`H^p(i_*E) = i_*H^p(E)`" of Stacks 09VA.

A complex `𝒦` representing `E` represents `Ri_*E` after degreewise pushforward
(`AlgebraicGeometry.RingedSpace.derivedPushforwardOXModFactors`), and the cohomology of `i_*𝒦` is
the pushforward of the cohomology of `𝒦` by
`AlgebraicGeometry.RingedSpace.homologyPushforwardComplexIso`. -/
public def homologyDerivedPushforwardOXModIso (hi : Topology.IsClosedEmbedding i.hom.base)
    (E : DerivedCategory (OXMod.{u, u} Z)) (j : ℤ) :
    (DerivedCategory.homologyFunctor (OXMod.{u, u} X) j).obj
        ((derivedPushforwardOXMod i hi).obj E) ≅
      (pushforwardOXMod i).obj
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} Z) j).obj E) := by
  letI K := DerivedCategory.Q.objPreimage E
  have e : DerivedCategory.Q.obj K ≅ E := Functor.objObjPreimageIso DerivedCategory.Q E
  have e1 := (DerivedCategory.homologyFunctor (OXMod.{u, u} X) j).mapIso
    ((derivedPushforwardOXMod i hi).mapIso e.symm ≪≫ (derivedPushforwardOXModFactors i hi).app K)
  have e2 := derivedHomologyIso
    (((pushforwardOXMod i).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) j
  have e3 := homologyPushforwardComplexIso i hi K j
  have e4 := (pushforwardOXMod i).mapIso ((derivedHomologyIso K j).symm ≪≫
    (DerivedCategory.homologyFunctor (OXMod.{u, u} Z) j).mapIso e)
  exact e1 ≪≫ e2 ≪≫ e3 ≪≫ e4

/-- **A bound on the cohomology of `Ri_*E` is a bound on the cohomology of `E`.** If the degree-`j`
cohomology of `Ri_*E` vanishes then so does that of `E`.

`H^j(Ri_*E) = i_*H^j(E)` and `i_*` reflects zero objects. Together with
`AlgebraicGeometry.RingedSpace.exists_isZero_homology_gt_derivedRestrict` this is the reduction
"after shrinking `X` we may assume `i_*E` and hence `E` is bounded above" of the converse half of
Stacks 09VA. -/
public theorem isZero_homology_of_isZero_homology_derivedPushforward
    (hi : Topology.IsClosedEmbedding i.hom.base) (E : DerivedCategory (OXMod.{u, u} Z)) (j : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) j).obj
      ((derivedPushforwardOXMod i hi).obj E))) :
    IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} Z) j).obj E) :=
  isZero_of_isZero_pushforwardOXMod i hi.toIsInducing
    (IsZero.of_iso h (homologyDerivedPushforwardOXModIso i hi E j).symm)

/-- **Stacks 08DN(1) read through `i_*`.** Let `i : Z ⟶ X` be a morphism of ringed spaces whose
underlying continuous map is a closed embedding, let `E ∈ D(𝒪_Z)` be such that `Ri_*E` is
`m`-pseudo-coherent, and let `p ≥ m` be such that the cohomology of `E` vanishes above `p`. Then
`H^p(E)` is an `𝒪_Z`-module of finite type.

`i_*` is exact, so the cohomology of `Ri_*E` vanishes above `p` as well; `Ri_*E` is
`p`-pseudo-coherent because `m ≤ p`, so Stacks 08DN(1) makes `H^p(Ri_*E) = i_*H^p(E)` an
`𝒪_X`-module of finite type, and
`AlgebraicGeometry.RingedSpace.isFiniteType_of_isFiniteType_pushforward` brings that down to `Z`.

This is the step of the converse half of Stacks 09VA which produces the finite free module mapping
onto the top cohomology sheaf. -/
public theorem isFiniteType_homology_of_isPseudoCoherentFrom_derivedPushforward
    (hi : Topology.IsClosedEmbedding i.hom.base) (E : DerivedCategory (OXMod.{u, u} Z)) (m p : ℤ)
    (hmp : m ≤ p)
    (h : IsPseudoCoherentFrom ((derivedPushforwardOXMod i hi).obj E) m)
    (hvanish : ∀ j : ℤ, p < j →
      IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} Z) j).obj E)) :
    SheafOfModules.IsFiniteType (R := structureSheafOfRings Z)
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} Z) p).obj E) := by
  have hX := isFiniteType_homology_of_isPseudoCoherentFrom
    ((derivedPushforwardOXMod i hi).obj E) p (h.mono hmp)
    fun j hj => isZero_homology_derivedPushforward i hi E j (hvanish j hj)
  refine isFiniteType_of_isFiniteType_pushforward i hi _ ?_
  exact SheafOfModules.IsFiniteType.of_iso (R := structureSheafOfRings X) hX
    (homologyDerivedPushforwardOXModIso i hi E p)

end Derived

end AlgebraicGeometry.RingedSpace

end
