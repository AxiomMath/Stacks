module

public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import
  StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.SectionsFunctionField
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Qcqs
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic

/-!
# Flat base change preserves finiteness of a module of sections

Let

```
Y --p--> X
|        |
k        iX
v        v
T --q--> S
```

be a cartesian square of schemes with `S` and `T` affine, `q` flat and `X` quasi-compact and
quasi-separated, and let `F` be a quasi-coherent `𝒪_X`-module whose sections over `X` are a finite
`Γ(S, ⊤)`-module. Then the sections of `p^* F` over `Y` are a finite `Γ(T, ⊤)`-module.

Specialised to the structure sheaf and to the cartesian square of an open subscheme and its
preimage, this says: for a flat morphism `q : T ⟶ S` of affine schemes and a quasi-compact,
quasi-separated open `W` of `S`, finiteness of `Γ(S, W)` over `Γ(S, ⊤)` gives finiteness of
`Γ(T, q⁻¹ W)` over `Γ(T, ⊤)`.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.CodimensionOneObstruction`.

* `moduleFinite_sections_pullback`: the statement above for a quasi-coherent module.
* `moduleFinite_sections_toScheme_of_isPullback`: its case `F = 𝒪_X`, stated for the rings of
  global sections.
* `moduleFinite_sections_toScheme_iff`: the sections of an open subscheme over the global sections
  are the sections over the open, as a module over the global sections.
* `moduleFinite_sections_preimage_of_flat`: the case of the cartesian square of an open and its
  preimage.
* `moduleFinite_sections_restrict_iff`: finiteness of the sections over `V₀ ∩ U` read on the open
  subscheme `V₀` and read on `X`.
* `noetherianSpace_toScheme`: an open subscheme of a Noetherian scheme is a Noetherian space, hence
  quasi-compact and quasi-separated.

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0AWC](https://stacks.math.columbia.edu/tag/0AWC)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.SectionsBaseChange
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.CodimensionOneObstruction

variable {S T X Y : Scheme.{u}}

/-! ### Transport of finiteness between restrictions of scalars -/

/-- Finiteness for a restriction of scalars along `φ : A →+* R` is transported by an `R`-linear
equivalence. -/
private theorem moduleFinite_compHom_of_linearEquiv {A R M N : Type*} [CommRing A] [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (φ : A →+* R)
    (e : M ≃ₗ[R] N) (h : @Module.Finite A M _ _ (Module.compHom M φ)) :
    @Module.Finite A N _ _ (Module.compHom N φ) :=
  let _ := Module.compHom M φ
  let _ := Module.compHom N φ
  Module.Finite.equiv (R := A) (M := M) (N := N)
    { toFun := e
      map_add' := e.map_add
      map_smul' := fun a x => e.map_smul (φ a) x
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv }

/-- Finiteness of an algebra is transported by a pair of ring isomorphisms commuting with the two
structure maps. -/
private theorem moduleFinite_ringEquiv_comm_iff {A₁ B₁ A₂ B₂ : Type*} [CommRing A₁] [CommRing B₁]
    [CommRing A₂] [CommRing B₂] [Algebra A₁ B₁] [Algebra A₂ B₂] (e₁ : A₁ ≃+* A₂) (e₂ : B₁ ≃+* B₂)
    (he : ∀ a, algebraMap A₂ B₂ (e₁ a) = e₂ (algebraMap A₁ B₁ a)) :
    Module.Finite A₁ B₁ ↔ Module.Finite A₂ B₂ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact Module.Finite.of_equiv_equiv e₁ e₂ (RingHom.ext he)
  · refine Module.Finite.of_equiv_equiv e₁.symm e₂.symm (RingHom.ext fun a => ?_)
    refine e₂.injective ?_
    show e₂ (algebraMap A₁ B₁ (e₁.symm a)) = e₂ (e₂.symm (algebraMap A₂ B₂ a))
    rw [e₂.apply_symm_apply, ← he, e₁.apply_symm_apply]

/-- A composite of restriction maps of a presheaf is the restriction map between the end opens. -/
private theorem presheaf_map_comp_eq_map {U₁ U₂ U₃ : X.Opens} (f : U₁ ⟶ U₂) (g : U₃ ⟶ U₁) :
    X.presheaf.map f.op ≫ X.presheaf.map g.op = X.presheaf.map (homOfLE (g.le.trans f.le)).op := by
  rw [← Functor.map_comp]
  rfl

/-! ### Quasi-compactness and quasi-separatedness of an open subscheme -/

/-- **An open subscheme of a Noetherian scheme is a Noetherian space**, and therefore both
quasi-compact and quasi-separated. -/
theorem noetherianSpace_toScheme [NoetherianSpace X] (W : X.Opens) :
    NoetherianSpace W.toScheme :=
  inferInstanceAs (NoetherianSpace (W : Set X))

/-! ### Flat base change of a module of sections -/

/-- **Finiteness of the sections of a quasi-coherent module is preserved by flat base change.** For
a cartesian square `IsPullback p k iX q` with `S` and `T` affine, `q` flat and `X` quasi-compact
and quasi-separated, and a quasi-coherent `𝒪_X`-module `F` whose sections over `X` are a finite
`Γ(S, ⊤)`-module, the sections of `p^* F` over `Y` are a finite `Γ(T, ⊤)`-module.

The scalar structures are restriction of scalars along the morphisms of the square. -/
theorem moduleFinite_sections_pullback
    {q : T ⟶ S} {iX : X ⟶ S} {p : Y ⟶ X} {k : Y ⟶ T} (H : IsPullback p k iX q)
    [IsAffine S] [IsAffine T] [Flat q] [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsQuasicoherent]
    (h : letI := baseModule iX F ⊤; Module.Finite Γ(S, ⊤) Γ(F, ⊤)) :
    letI := baseModule k ((Scheme.Modules.pullback p).obj F) ⊤
    Module.Finite Γ(T, ⊤) Γ((Scheme.Modules.pullback p).obj F, ⊤) := by
  let _ := baseAlgebra q
  let _ := baseModule iX F ⊤
  let _ := baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) ⊤
  let _ := baseModule k ((Scheme.Modules.pullback p).obj F) ⊤
  let _ := baseTower H ((Scheme.Modules.pullback p).obj F) ⊤
  obtain ⟨e, -⟩ := exists_linearEquiv_sections_baseChange H F
  have : Module.Finite Γ(T, ⊤) (Γ(T, ⊤) ⊗[Γ(S, ⊤)] Γ(F, ⊤)) :=
    Module.Finite.base_change _ _ _
  exact Module.Finite.equiv e

/-- **Finiteness of the ring of global sections is preserved by flat base change.** This is the
previous statement for the structure sheaf: for a cartesian square `IsPullback p k iX q` with `S`
and `T` affine, `q` flat and `X` quasi-compact and quasi-separated, finiteness of `Γ(X, ⊤)` over
`Γ(S, ⊤)` gives finiteness of `Γ(Y, ⊤)` over `Γ(T, ⊤)`. -/
theorem moduleFinite_sections_toScheme_of_isPullback
    {q : T ⟶ S} {iX : X ⟶ S} {p : Y ⟶ X} {k : Y ⟶ T} (H : IsPullback p k iX q)
    [IsAffine S] [IsAffine T] [Flat q] [CompactSpace X] [QuasiSeparatedSpace X]
    (h : letI := baseAlgebra iX; Module.Finite Γ(S, ⊤) Γ(X, ⊤)) :
    letI := baseAlgebra k; Module.Finite Γ(T, ⊤) Γ(Y, ⊤) := by
  let UX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let UY : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  have : UX.IsQuasicoherent := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X
  let α : (Scheme.Modules.pullback p).obj UX ≅ UY := Scheme.Modules.pullbackUnitIso p
  exact moduleFinite_compHom_of_linearEquiv _
    { (asIso (α.hom.app ⊤)).addCommGroupIsoToAddEquiv with
      map_smul' := fun r x => Scheme.Modules.Hom.app_smul α.hom r x }
    (moduleFinite_sections_pullback H UX h)

/-- **The global sections of an open subscheme are the sections over the open**, as a module over
the global sections of the ambient scheme: finiteness of one is finiteness of the other. -/
theorem moduleFinite_sections_toScheme_iff (W : X.Opens) :
    (letI := baseAlgebra W.ι; Module.Finite Γ(X, ⊤) Γ(W.toScheme, ⊤)) ↔
      letI := resAlgebra (le_top (a := W)); Module.Finite Γ(X, ⊤) Γ(X, W) := by
  have key : W.ι.appLE ⊤ ⊤ (le_preimage_top W.ι ⊤) ≫ W.topIso.hom
      = X.presheaf.map (homOfLE (le_top (a := W))).op := by
    simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_hom]
    exact presheaf_map_comp_eq_map _ _
  let _ := baseAlgebra W.ι
  let _ := resAlgebra (le_top (a := W))
  exact moduleFinite_ringEquiv_comm_iff (RingEquiv.refl _) W.topIso.commRingCatIsoToRingEquiv
    fun a => congrArg (fun f => f.hom a) key.symm

/-- **Finiteness of the sections over an open is preserved by flat base change.** Let `q : T ⟶ S`
be a flat morphism of affine schemes and let `W` be a quasi-compact, quasi-separated open of `S`.
If `Γ(S, W)` is a finite `Γ(S, ⊤)`-module, then `Γ(T, q⁻¹ W)` is a finite `Γ(T, ⊤)`-module. -/
theorem moduleFinite_sections_preimage_of_flat (q : T ⟶ S) [IsAffine S] [IsAffine T] [Flat q]
    (W : S.Opens) [CompactSpace W.toScheme] [QuasiSeparatedSpace W.toScheme]
    (h : letI := resAlgebra (le_top (a := W)); Module.Finite Γ(S, ⊤) Γ(S, W)) :
    letI := resAlgebra (le_top (a := q ⁻¹ᵁ W)); Module.Finite Γ(T, ⊤) Γ(T, q ⁻¹ᵁ W) :=
  (moduleFinite_sections_toScheme_iff _).mp
    (moduleFinite_sections_toScheme_of_isPullback (isPullback_morphismRestrict q W)
      ((moduleFinite_sections_toScheme_iff W).mpr h))

/-- **The sections of an open subscheme over an open of it are the sections of the ambient scheme
over the intersection.** For opens `V₀` and `U` of `X`, the sections of the open subscheme `V₀`
over `V₀ ∩ U` are a finite module over the global sections of `V₀` exactly when `Γ(X, U ⊓ V₀)` is a
finite `Γ(X, V₀)`-module. -/
theorem moduleFinite_sections_restrict_iff (V₀ U : X.Opens) :
    (letI := resAlgebra (le_top (a := V₀.ι ⁻¹ᵁ U));
      Module.Finite Γ(V₀.toScheme, ⊤) Γ(V₀.toScheme, V₀.ι ⁻¹ᵁ U)) ↔
      letI := resAlgebra (inf_le_right : U ⊓ V₀ ≤ V₀); Module.Finite Γ(X, V₀) Γ(X, U ⊓ V₀) := by
  have himg : V₀.ι ''ᵁ (V₀.ι ⁻¹ᵁ U) = U ⊓ V₀ := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm]
  let _ := resAlgebra (le_top (a := V₀.ι ⁻¹ᵁ U))
  let _ := resAlgebra (inf_le_right : U ⊓ V₀ ≤ V₀)
  let e₂ : Γ(V₀.toScheme, V₀.ι ⁻¹ᵁ U) ≅ Γ(X, U ⊓ V₀) :=
    X.presheaf.mapIso (eqToIso himg.symm).op
  have key : V₀.toScheme.presheaf.map (homOfLE (le_top (a := V₀.ι ⁻¹ᵁ U))).op ≫ e₂.hom
      = V₀.topIso.hom ≫ X.presheaf.map (homOfLE (inf_le_right : U ⊓ V₀ ≤ V₀)).op := by
    simp only [Scheme.Opens.toScheme_presheaf_map, Scheme.Opens.topIso_hom, e₂]
    exact (presheaf_map_comp_eq_map _ _).trans (presheaf_map_comp_eq_map _ _).symm
  exact moduleFinite_ringEquiv_comm_iff V₀.topIso.commRingCatIsoToRingEquiv
    e₂.commRingCatIsoToRingEquiv
    fun a => (congrArg (fun m : Γ(V₀.toScheme, ⊤) ⟶ Γ(X, U ⊓ V₀) => m.hom a) key).symm

end Stacks.AlgebraicGeometry.CodimensionOneObstruction

end
