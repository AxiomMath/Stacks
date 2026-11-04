module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexBaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexUniqueIso
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexOfProperFlat
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexExistence
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexBaseChangeTheorem
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.AlongAnIsomorphism

/-!
# The relative dualizing complex `a(𝒪_{S'})` and base change

Let `f : X ⟶ S` be flat, proper and of finite presentation. By Stacks 0E2X there is a relative
dualizing complex `(ω_{X/S}^•, ξ)` for `f` in the sense of Stacks 0E2T, relative to any open
`W ⊆ X ×_S X` through which the relative diagonal factors as a closed immersion. Let
`g : S' ⟶ S` be a morphism with `S'` quasi-compact and quasi-separated, `f' : X' ⟶ S'` the base
change and `g' : X' ⟶ X` the projection. By Stacks 0E2Y, `(L(g')^*ω_{X/S}^•, L(g')^*ξ)` is a
relative dualizing complex for `f'`, relative to any open `W' ⊆ X' ×_{S'} X'` through which the
relative diagonal of `f'` factors as a closed immersion and which `g' × g'` maps into `W`. By
Stacks 0E2Z, `ω_{X'/S'}^• = a'(𝒪_{S'})` together with the map coming from Equation 0E2Q is a
relative dualizing complex for `f'` on `X' ×_{S'} X'`; restricted to `W'`, it is one there. By
Stacks 0E2W there is then a unique isomorphism `ω_{X'/S'}^• ⟶ L(g')^*ω_{X/S}^•` compatible with
(0E2Q) and `L(g')^*ξ` (Stacks 0E4P).

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.restrictDiagonalMap`: the restriction of a map
  `ξ : Δ_*𝒪_X ⟶ L pr₁^*K|_W` to a smaller diagonal open `W' ⊆ W`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.existsUnique_relativeDualizingComplex_iso_baseChange`: the
  unique isomorphism `a'(𝒪_{S'}) ≅ L(g')^*ω_{X/S}^•` compatible with (0E2Q) and `L(g')^*ξ`.
* `AlgebraicGeometry.Scheme.Hom.relativeDualizingComplex_baseChange_twistedInverseImage`:
  Stacks 0E4P, the existence of `(ω_{X/S}^•, ξ)` together with that isomorphism for every
  `S' ⟶ S` with `S'` quasi-compact and quasi-separated.

## Implementation notes

The source closes the remark by saying that these isomorphisms are compatible with morphisms
between quasi-compact and quasi-separated schemes over `S` and with the base change isomorphisms
of Stacks 0AAB, and that this compatibility would be carefully stated and proved if ever needed.
That sentence states no assertion with a proof, and it is not formalized here.

The derived categories are those of `HasDerivedCategory.standard`, the model at which relative
dualizing complexes (Stacks 0E2T) and the complex `a(𝒪_S)` of Stacks 0E2Z are stated.

## References

* [Stacks Project, Remark 48.28.9 (Tag 0E4P)](https://stacks.math.columbia.edu/tag/0E4P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance 10000] HasDerivedCategory.standard

/-- The identity square `X = X ×_S S` of a morphism `f : X ⟶ S`. -/
theorem isPullback_id {X S : Scheme.{u}} (f : X ⟶ S) : IsPullback (𝟙 X) f f (𝟙 S) :=
  IsPullback.of_id_fst

/-- Along the identity square, `g' × g'` is the identity of `X ×_S X`. -/
theorem pullbackMapOfIsPullback_isPullback_id {X S : Scheme.{u}} (f : X ⟶ S) :
    pullbackMapOfIsPullback (isPullback_id f) = 𝟙 _ := by
  ext <;> simp

namespace DiagonalOpen

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- `L(𝟙_X)^* ≅ 𝟭` on `D(𝒪_X)`. -/
def derivedPullbackIdIso (X : Scheme.{u}) :
    derivedPullback (Scheme.Hom.toLRSHom (𝟙 X)).toShHom ≅
      𝟭 (DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :=
  Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackIdIso X.toRingedSpace

variable (D D' : DiagonalOpen f) (w : D'.W ⟶ D.W) (hw : w ≫ D.ι = D'.ι)

include hw in
/-- If `w : W' ⟶ W` lies over `X ×_S X`, then it lies over the map `g' × g'` of the identity
square of `f`. -/
theorem comp_ι_eq_isPullback_id : w ≫ D.ι = D'.ι ≫ pullbackMapOfIsPullback (isPullback_id f) := by
  rw [pullbackMapOfIsPullback_isPullback_id, Category.comp_id, hw]

/-- **Restriction of `ξ` to a smaller diagonal open.** For diagonal opens `W' ⊆ W` of `f`, given
by `w : W' ⟶ W` over `X ×_S X`, the restriction of `ξ : Δ_*𝒪_X ⟶ L pr₁^*K|_W` to `W'`: the
derived base change of `ξ` along the identity square of `f` followed by `L(𝟙_X)^*K ≅ K`. -/
def restrictDiagonalMap [Flat f] (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K) :
    D'.diagonalObject ⟶ D'.derivedPullbackProj K :=
  D.baseChangeDiagonalMap D' (𝟙 X) w
      (proj_baseChange (isPullback_id f) D D' w (comp_ι_eq_isPullback_id D D' w hw))
      (baseChangeDiagonalIso (isPullback_id f) D D' w (comp_ι_eq_isPullback_id D D' w hw)) K ξ ≫
    D'.derivedPullbackProjMap ((derivedPullbackIdIso X).hom.app K)

/-- Composing the restriction of `ξ` with `L pr₁^*(a)|_{W'}` for `a : K ⟶ L`. -/
theorem restrictDiagonalMap_comp_map [Flat f] {K L : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
    (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K) (a : K ⟶ L) :
    D.restrictDiagonalMap D' w hw K ξ ≫ D'.derivedPullbackProjMap a =
      D.baseChangeDiagonalMap D' (𝟙 X) w
          (proj_baseChange (isPullback_id f) D D' w (comp_ι_eq_isPullback_id D D' w hw))
          (baseChangeDiagonalIso (isPullback_id f) D D' w (comp_ι_eq_isPullback_id D D' w hw))
          K ξ ≫
        D'.derivedPullbackProjMap ((derivedPullbackIdIso X).hom.app K ≫ a) := by
  rw [restrictDiagonalMap, Category.assoc]
  exact congrArg (fun t => _ ≫ t)
    ((derivedPullback D'.proj.toLRSHom.toShHom).map_comp _ a).symm

end DiagonalOpen

/-- For a separated `f`, every diagonal open `W` of `f` lies over the diagonal open
`X ×_S X` given by `DiagonalOpen.ofIsSeparated f`, via its own inclusion. -/
theorem DiagonalOpen.comp_ι_ofIsSeparated {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    (D : DiagonalOpen f) : D.ι ≫ (DiagonalOpen.ofIsSeparated f).ι = D.ι :=
  Category.comp_id _

/-- **The unique isomorphism `a'(𝒪_{S'}) ≅ L(g')^*ω_{X/S}^•`.** Let `f : X ⟶ S` be flat,
proper and of finite presentation, `(K, ξ)` a relative dualizing complex for `f` relative to the
diagonal open `W`, and `X' = X ×_S S'` for `g : S' ⟶ S` with `S'` quasi-compact and
quasi-separated. For a diagonal open `W'` of `f' : X' ⟶ S'` mapped into `W` by `g' × g'`, there
is a unique isomorphism `φ : a'(𝒪_{S'}) ≅ L(g')^*K` sending the map of Equation 0E2Q, restricted
to `W'`, to the derived base change `L(g')^*ξ`. -/
theorem existsUnique_relativeDualizingComplex_iso_baseChange {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] {D : DiagonalOpen f}
    {K : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
    {ξ : D.diagonalObject ⟶ D.derivedPullbackProj K}
    (hK : IsRelativeDualizingComplex f (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
      (RingedSpace.inverseImage S.toRingedSpace f.base)) D K ξ)
    {X' S' : Scheme.{u}} [CompactSpace S'] [QuasiSeparatedSpace S'] {g : S' ⟶ S}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} (hpb : IsPullback g' f' f g)
    (D' : DiagonalOpen f') (w : D'.W ⟶ D.W) (hw : w ≫ D.ι = D'.ι ≫ pullbackMapOfIsPullback hpb) :
    haveI : IsProper f' := MorphismProperty.of_isPullback (P := @IsProper) hpb inferInstance
    haveI : Flat f' := MorphismProperty.of_isPullback (P := @Flat) hpb inferInstance
    haveI : LocallyOfFinitePresentation f' :=
      MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hpb inferInstance
    haveI : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace f'
    haveI : QuasiSeparatedSpace X' := quasiSeparatedSpace_of_quasiSeparated f'
    haveI : CompactSpace (pullback f' f' : Scheme.{u}) :=
      QuasiCompact.compactSpace_of_compactSpace (pullback.fst f' f')
    haveI : QuasiSeparatedSpace (pullback f' f' : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.fst f' f')
    ∃! φ : (Stacks.Duality.StandardModel.relativeDualizingComplex f').obj ≅
        DiagonalOpen.baseChangeComplex g' K,
      (DiagonalOpen.ofIsSeparated f').restrictDiagonalMap D' D'.ι
          (DiagonalOpen.comp_ι_ofIsSeparated f' D')
          (Stacks.Duality.StandardModel.relativeDualizingComplex f').obj
          (Stacks.Duality.relativeDualizingComplexDiagonalMap f') ≫
          D'.derivedPullbackProjMap φ.hom =
        D.baseChangeDiagonalMap D' g' w (DiagonalOpen.proj_baseChange hpb D D' w hw)
          (DiagonalOpen.baseChangeDiagonalIso hpb D D' w hw) K ξ := by
  have : IsProper f' := MorphismProperty.of_isPullback (P := @IsProper) hpb inferInstance
  have : Flat f' := MorphismProperty.of_isPullback (P := @Flat) hpb inferInstance
  have : LocallyOfFinitePresentation f' :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hpb inferInstance
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace f'
  have : QuasiSeparatedSpace X' := quasiSeparatedSpace_of_quasiSeparated f'
  have : CompactSpace (pullback f' f' : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst f' f')
  have : QuasiSeparatedSpace (pullback f' f' : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst f' f')
  have h₁ := (Stacks.Duality.isRelativeDualizingComplex_relativeDualizingComplex f').baseChange
    (isPullback_id f') D' D'.ι
    (DiagonalOpen.comp_ι_eq_isPullback_id (DiagonalOpen.ofIsSeparated f') D' D'.ι
      (DiagonalOpen.comp_ι_ofIsSeparated f' D'))
  obtain ⟨e, he, huniq⟩ := h₁.existsUnique_iso (hK.baseChange hpb D' w hw)
  let ι₀ := (DiagonalOpen.derivedPullbackIdIso X').app
    (Stacks.Duality.StandardModel.relativeDualizingComplex f').obj
  refine ⟨ι₀.symm ≪≫ e, ?_, fun φ hφ => ?_⟩
  · refine (DiagonalOpen.restrictDiagonalMap_comp_map _ _ _ _ _ _).trans
      ((congrArg (fun t => _ ≫ D'.derivedPullbackProjMap t) ?_).trans he)
    exact ι₀.hom_inv_id_assoc e.hom
  · have h : ι₀ ≪≫ φ = e :=
      huniq _ ((DiagonalOpen.restrictDiagonalMap_comp_map _ _ _ _ _ _).symm.trans hφ)
    rw [← h]
    ext
    exact (ι₀.inv_hom_id_assoc φ.hom).symm

/-- **Relative dualizing complexes and base change.** Let `f : X ⟶ S` be flat, proper and of
finite presentation, and let `W` be a diagonal open of `f`. There is a relative dualizing complex
`(ω_{X/S}^•, ξ)` for `f` relative to `W` (Stacks 0E2X), and for every such pair, every morphism
`g : S' ⟶ S` with `S'` quasi-compact and quasi-separated, with base change `f' : X' ⟶ S'` and
projection `g' : X' ⟶ X`, and every diagonal open `W'` of `f'` mapped into `W` by `g' × g'`,
there is a unique isomorphism `ω_{X'/S'}^• = a'(𝒪_{S'}) ≅ L(g')^*ω_{X/S}^•` compatible with the
map of Equation 0E2Q (restricted to `W'`) and the derived base change `L(g')^*ξ` of
Stacks 0E2Y. -/
@[stacks 0E4P]
theorem relativeDualizingComplex_baseChange_twistedInverseImage {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] (D : DiagonalOpen f) :
    (∃ (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
      (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K),
      IsRelativeDualizingComplex f (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base)) D K ξ) ∧
    ∀ (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
      (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K),
      IsRelativeDualizingComplex f (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base)) D K ξ →
      ∀ {X' S' : Scheme.{u}} [CompactSpace S'] [QuasiSeparatedSpace S'] {g : S' ⟶ S}
        {g' : X' ⟶ X} {f' : X' ⟶ S'} (hpb : IsPullback g' f' f g)
        (D' : DiagonalOpen f') (w : D'.W ⟶ D.W)
        (hw : w ≫ D.ι = D'.ι ≫ pullbackMapOfIsPullback hpb),
        haveI : IsProper f' := MorphismProperty.of_isPullback (P := @IsProper) hpb inferInstance
        haveI : Flat f' := MorphismProperty.of_isPullback (P := @Flat) hpb inferInstance
        haveI : LocallyOfFinitePresentation f' :=
          MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hpb inferInstance
        haveI : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace f'
        haveI : QuasiSeparatedSpace X' := quasiSeparatedSpace_of_quasiSeparated f'
        haveI : CompactSpace (pullback f' f' : Scheme.{u}) :=
          QuasiCompact.compactSpace_of_compactSpace (pullback.fst f' f')
        haveI : QuasiSeparatedSpace (pullback f' f' : Scheme.{u}) :=
          quasiSeparatedSpace_of_quasiSeparated (pullback.fst f' f')
        ∃! φ : (Stacks.Duality.StandardModel.relativeDualizingComplex f').obj ≅
            DiagonalOpen.baseChangeComplex g' K,
          (DiagonalOpen.ofIsSeparated f').restrictDiagonalMap D' D'.ι
              (DiagonalOpen.comp_ι_ofIsSeparated f' D')
              (Stacks.Duality.StandardModel.relativeDualizingComplex f').obj
              (Stacks.Duality.relativeDualizingComplexDiagonalMap f') ≫
              D'.derivedPullbackProjMap φ.hom =
            D.baseChangeDiagonalMap D' g' w (DiagonalOpen.proj_baseChange hpb D D' w hw)
              (DiagonalOpen.baseChangeDiagonalIso hpb D D' w hw) K ξ :=
  ⟨exists_isRelativeDualizingComplex_canonicalFamily D, fun _ _ hK _ _ _ _ _ _ _ hpb D' w hw =>
    existsUnique_relativeDualizingComplex_iso_baseChange f hK hpb D' w hw⟩

end AlgebraicGeometry.Scheme.Hom

end
