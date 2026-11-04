module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NormalizedProper
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekCohenMacaulayTwistIso
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekRelativeTorDimension

/-!
# Normalized dualizing complexes and Cohen–Macaulay morphisms

Let `S` be Noetherian with a dualizing complex `ω_S^•`, and `f : X ⟶ Y` a separated
Cohen–Macaulay morphism of relative dimension `d` between schemes of finite type over `S`, not
necessarily separated over `S`. For the upper shriek functors of a choice of compactifications,
with `ω_X^•`, `ω_Y^•` the dualizing complexes normalized relative to `ω_S^•` and
`ω_{X/Y} = H^{-d}(f^! 𝒪_Y)`,

`ω_X^• ≅ Lf^* ω_Y^• ⊗ᴸ ω_{X/Y}[d]`,

and if `Y` is connected and Cohen–Macaulay, `ω_X = f^* ω_Y ⊗ ω_{X/Y}` for the unique nonzero
cohomology sheaves. This is the last sentence of [Stacks, Tag 0C10]: `ω_X^• ≅ f^! ω_Y^•`
(`Stacks.Duality.NormalizedOnOpens.upperShriekObjIso`) reduces it to the separated case.
Likewise for `f` flat and proper, `ω_X^• ≅ a(ω_Y^•) ≅ Lf^* ω_Y^• ⊗ᴸ a(𝒪_Y)`
([Stacks, Tag 0B6W]).

## Main results

* `Stacks.Duality.NormalizedOnOpens.nonempty_iso_pullback_tensor_shift_ofCompactifications`
* `Stacks.Duality.NormalizedOnOpens.exists_homology_iso_pullback_tensor_ofCompactifications`
* `Stacks.Duality.NormalizedOnOpens.nonempty_iso_pullback_tensor_of_flat`: [Stacks, Tag 0B6W].

## References

* [Stacks Project, Tag 0C10](https://stacks.math.columbia.edu/tag/0C10)
* [Stacks Project, Tag 0B6U](https://stacks.math.columbia.edu/tag/0B6U)
* [Stacks Project, Tag 0B6W](https://stacks.math.columbia.edu/tag/0B6W)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

namespace NormalizedOnOpens

variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f → CompactificationOf (Over.mk f))
  {X Y S : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ S} {p : X ⟶ S} (hpe : f ≫ q = p)
  {hp : IsFiniteTypeOverNoetherian p} {hq : IsFiniteTypeOverNoetherian q}
  {ωS : quasiCoherentDerivedCategoryPlusOfModel S}

include hpe in
/-- **[Stacks, Tag 0C10], last sentence, the complexes**, for the upper shriek functors of
compactifications: for a separated Cohen–Macaulay `f : X ⟶ Y` of relative dimension `d` between
schemes of finite type over `S`, the dualizing complexes normalized relative to `ω_S^•` satisfy
`ω_X^• ≅ Lf^* ω_Y^• ⊗ᴸ ω_{X/Y}[d]`, where `ω_{X/Y} = H^{-d}(f^! 𝒪_Y)`. -/
theorem nonempty_iso_pullback_tensor_shift_ofCompactifications
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) (hf : IsShriekable f)
    (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
    (𝒦Y : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS)
    (hCM : haveI := hf.target_noetherian
      (ftsHomOf f hf.separatedFiniteType (isSeparatedFiniteType_id Y)
        (Category.comp_id f)).left.IsCohenMacaulay (isLocallyNoetherian_fiber_left _))
    (d : ℕ) (hd : ∀ x : X, topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
      (d : WithBot ℕ∞)) :
    haveI := hf.target_noetherian
    Nonempty (𝒦X.complex.obj ≅ ((quasiCoherentDerivedTensor X).obj
        ((quasiCoherentDerivedPullback' f).obj 𝒦Y.complex.obj)).obj
          (relativeDualizingSheafShift (ftsHomOf f hf.separatedFiniteType
            (isSeparatedFiniteType_id Y) (Category.comp_id f)) (c f hf) hCM d hd)) := by
  have := hf.target_noetherian
  obtain ⟨e⟩ := nonempty_upperShriek_iso_pullback_tensor_shift
    (ftsHomOf f hf.separatedFiniteType (isSeparatedFiniteType_id Y) (Category.comp_id f))
    (c f hf) hCM d hd 𝒦Y.complex.obj 𝒦Y.complex.property
  exact ⟨(ObjectProperty.ι _).mapIso (upperShriekObjIso c hpe hωS hf 𝒦X 𝒦Y) ≪≫ e⟩

include hpe in
/-- **[Stacks, Tag 0C10], last sentence, the dualizing modules**, for the upper shriek functors
of compactifications: if moreover `Y` is connected and Cohen–Macaulay, the normalized complexes
`ω_Y^•` and `ω_X^•` are concentrated in single degrees `m` and `m - d`, and their cohomology
sheaves there satisfy `ω_X ≅ f^* ω_Y ⊗ ω_{X/Y}`. -/
theorem exists_homology_iso_pullback_tensor_ofCompactifications
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) (hf : IsShriekable f)
    (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
    (𝒦Y : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS)
    (hCM : haveI := hf.target_noetherian
      (ftsHomOf f hf.separatedFiniteType (isSeparatedFiniteType_id Y)
        (Category.comp_id f)).left.IsCohenMacaulay (isLocallyNoetherian_fiber_left _))
    (d : ℕ) (hd : ∀ x : X, topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
      (d : WithBot ℕ∞))
    [ConnectedSpace Y] (hY : AlgebraicGeometry.IsCohenMacaulay Y) :
    haveI := hf.target_noetherian
    ∃ m : ℤ,
      (∀ i : ℤ, i ≠ m → IsZero ((DerivedCategory.homologyFunctor Y.Modules i).obj
        𝒦Y.complex.obj.obj)) ∧
      (∀ i : ℤ, i ≠ m - d → IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj
        𝒦X.complex.obj.obj)) ∧
      Nonempty ((DerivedCategory.homologyFunctor X.Modules (m - d)).obj 𝒦X.complex.obj.obj ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj
          ((Scheme.Modules.pullback f).obj
            ((DerivedCategory.homologyFunctor Y.Modules m).obj 𝒦Y.complex.obj.obj))).obj
          (relativeDualizingSheaf (ftsHomOf f hf.separatedFiniteType
            (isSeparatedFiniteType_id Y) (Category.comp_id f)) (c f hf) d)) := by
  have := hf.target_noetherian
  obtain ⟨e⟩ := nonempty_iso_pullback_tensor_shift_ofCompactifications c hpe hωS hf 𝒦X 𝒦Y hCM d hd
  have : ConnectedSpace (ftsOf (𝟙 Y) (isSeparatedFiniteType_id Y)).left := ‹ConnectedSpace Y›
  have := hq.source_noetherian
  exact exists_homology_iso_pullback_tensor_of_iso_shift
    (ftsHomOf f hf.separatedFiniteType (isSeparatedFiniteType_id Y) (Category.comp_id f))
    (c f hf) hCM d hd 𝒦Y.complex.obj 𝒦X.complex.obj hY
    (𝒦Y.isDualizingComplex_ofCompactifications c hωS) e

include hpe in
/-- **[Stacks, Tag 0B6W]** for the upper shriek functors of compactifications. Let `f : X ⟶ Y` be
a flat proper morphism of schemes of finite type over `S`, with `ω_X^•`, `ω_Y^•` the dualizing
complexes normalized relative to `ω_S^•`, `a` the right adjoint of `Rf_*` and
`ω_{X/Y}^• = a(𝒪_Y)` the relative dualizing complex. Then
`ω_X^• ≅ a(ω_Y^•) ≅ Lf^* ω_Y^• ⊗ᴸ ω_{X/Y}^•`; the first isomorphism is
`Stacks.Duality.NormalizedOnOpens.twistedInverseImageObjIso`, the second `μ` of
[Stacks, Tag 0B6U] for the perfect morphism `f`. -/
theorem nonempty_iso_pullback_tensor_of_flat
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) [IsProper f] [Flat f]
    (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
    (𝒦Y : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS) :
    haveI := hq.source_noetherian
    haveI := hp.source_noetherian
    Nonempty (𝒦X.complex.obj ≅ ((quasiCoherentDerivedTensor X).obj
        ((quasiCoherentDerivedPullback' f).obj 𝒦Y.complex.obj)).obj
          ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
            (DerivedPushforward.derivedStructureSheaf Y))) := by
  have := hq.source_noetherian
  have := hp.source_noetherian
  have hf := isShriekable_of_isProper hp hq (f := f)
  have := locallyOfFinitePresentation_left
    (ftsHomOf f hf.separatedFiniteType (isSeparatedFiniteType_id Y) (Category.comp_id f))
  have : Flat (ftsHomOf f hf.separatedFiniteType (isSeparatedFiniteType_id Y)
    (Category.comp_id f)).left := inferInstanceAs (Flat f)
  have : Perfect (ftsHomOf f hf.separatedFiniteType (isSeparatedFiniteType_id Y)
    (Category.comp_id f)).left := inferInstance
  obtain ⟨μ⟩ := nonempty_upperShriek_iso_pullback_tensor
    (ftsHomOf f hf.separatedFiniteType (isSeparatedFiniteType_id Y) (Category.comp_id f))
    (c f hf) 𝒦Y.complex.obj 𝒦Y.complex.property
  exact ⟨(twistedInverseImageObjIso c hpe hωS 𝒦X 𝒦Y).symm ≪≫
    ((UpperShriek.shriekOfIsoOfIsProper c f hf).app 𝒦Y.complex).symm ≪≫ μ.symm ≪≫
    ((quasiCoherentDerivedTensor X).obj
      ((quasiCoherentDerivedPullback' f).obj 𝒦Y.complex.obj)).mapIso
      ((UpperShriek.shriekOfIsoOfIsProper c f hf).app (derivedStructureSheafPlus Y))⟩

end NormalizedOnOpens

end Stacks.Duality

end
