module

public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.FiniteStageContinuity
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.QuasiCompactOpen
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.InvertibleDescent
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.NormalizedPullback
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.UniversalDirectImage
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.PicardChart.Basic

/-!
# Descent of a Galois-fixed Picard class along a finite Galois extension

Let `K/k` be a *finite* Galois extension, let `X` be a scheme over `k` with a `k`-rational
point and with `H⁰(X_K, 𝒪) = K`, and let `y` be a class of `Pic(X_K)` fixed by `Gal(K/k)`.
Then `y` is pulled back from `Pic(X)`. This is the heart of the surjectivity clause of
[Stacks, Tag 0CDT](https://stacks.math.columbia.edu/tag/0CDT); the reduction of an arbitrary
Galois extension to its finite Galois subextensions is
`StacksFrontier/AlgebraicGeometry/Picard/GaloisDescent/FiniteStageFixed.lean`, and the two are
assembled in `StacksFrontier/AlgebraicGeometry/Picard/GaloisDescent/PicardGaloisInvariants.lean`.

Fixedness of the class gives, for each `σ`, *some* isomorphism `ℒ ≅ f_σ^* ℒ` of the chosen
representative with its twist, and nothing in that says the family is a cocycle. What makes it
one is the rational point, in three steps.

* `Pic(Spec K) = 0`, so the restriction of `ℒ` to the induced `K`-rational point of `X_K` is
  trivialised. A field is a unique factorisation domain, so this is Tag 0BDA.
* The structure morphism `X_K ⟶ Spec K` has invariant structure sheaf: `H⁰(X_K, 𝒪) = K` is an
  isomorphism on global sections, and the spectrum of a field has only two opens, so it is an
  isomorphism of sheaves. Hence an isomorphism of invertible modules on `X_K` is determined by
  its restriction along the point, by
  `Stacks.Picard.existsUnique_sectionPullback_mapIso`.
* The family normalised against the trivialisation is a cocycle,
  `Stacks.Picard.twistNormalizedIso_mul` of `StacksFrontier/AlgebraicGeometry/Picard/GaloisDescent/NormalizedPullback.lean`. The point is
  equivariant — the twist `id_X × Spec(σ)` moves it by `Spec σ` — which is what puts the
  normalisation in the shape that lemma takes.

The cocycle is a Galois descent datum, and Tag 0CDR in invertible form,
`Stacks.Descent.exists_isInvertible_pullback_iso_of_galoisDescentData_baseChange`, descends it.

## Main definitions

* `Stacks.Picard.baseChangePoint` — the `K`-rational point of `X_K` induced by a `k`-rational
  point of `X`.

## Main results

* `Stacks.Picard.nonempty_iso_unitModule_spec` — **an invertible module on the spectrum of a
  field is trivial.**
* `Stacks.Picard.isIso_c_of_isIso_appTop_spec` — **`f_* 𝒪 = 𝒪` for a morphism to the spectrum of
  a field with invariant global sections.**
* `Stacks.Picard.baseChangePoint_comp_snd` and
  `Stacks.Picard.baseChangePoint_comp_galoisTwist` — the induced point is a section of the
  structure morphism of `X_K`, and it is equivariant.
* `Stacks.Picard.exists_isInvertible_pullback_iso_of_forall_nonempty_iso_galoisTwist` — the
  descent, for a module.
* `Stacks.Picard.exists_schemePullbackClass_eq_of_galoisFixed` — the descent, for a Picard
  class.

## Implementation notes

**Why the module statement is separate from the class statement.** The chosen representative of
a Picard class has the type `Stacks.Picard.picardRepresentative` gives it, which is the
ringed-space spelling of the modules on `X_K`; the scheme spelling `(X_K).Modules` is
definitionally equal to it but not at the transparency at which instance search runs, so an
`IsInvertible` hypothesis about the representative is not found as an instance for a lemma
stated about `(X_K).Modules`. Taking the module as a variable, as
`Stacks.Picard.exists_isInvertible_pullback_iso_of_forall_nonempty_iso_galoisTwist` does, keeps
the two apart: the class statement passes the representative across the definitional equality
once, in term position, where it is checked at default transparency.

**No `@[stacks]` attribute.** Tag 0CDR is the equivalence of categories and is registered where
it is proved; Tag 0CDT is registered on the identification itself, in
`StacksFrontier/AlgebraicGeometry/Picard/GaloisDescent/PicardGaloisInvariants.lean`.

## References

* [Stacks Project, Tag 0CDT](https://stacks.math.columbia.edu/tag/0CDT)
* [Stacks Project, Tag 0CDR](https://stacks.math.columbia.edu/tag/0CDR)
* [Stacks Project, Tag 0BDA](https://stacks.math.columbia.edu/tag/0BDA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.RingedSpace (structureIsSheaf)
open Stacks.SheafOfModules (picardClass picardClass_eq_iff)

universe u

namespace Stacks.Picard

/-! ### The spectrum of a field -/

/-- **The Picard group of the spectrum of a field is trivial**: an invertible module on
`Spec E` is isomorphic to the structure sheaf. A field is a unique factorisation domain, so
this is Tag 0BDA. -/
theorem nonempty_iso_unitModule_spec (E : Type u) [Field E] (L : (Spec (.of E)).Modules)
    (hL : Stacks.SheafOfModules.IsInvertible (Spec (.of E)).presheaf
      (Spec (.of E)).ringCatSheaf.2 L) :
    Nonempty (L ≅ Scheme.unitModule (Spec (.of E))) := by
  have hsub := Stacks.ProjectiveSpace.PicardChart.subsingleton_picardGroup_spectrum E
  have hU : Stacks.SheafOfModules.IsInvertible (Spec (.of E)).presheaf
      (Spec (.of E)).ringCatSheaf.2 (Scheme.unitModule (Spec (.of E))) :=
    inferInstanceAs (Stacks.SheafOfModules.IsInvertible (Spec (.of E)).presheaf
      (Spec (.of E)).ringCatSheaf.2 (SheafOfModules.unit (Spec (.of E)).ringCatSheaf))
  exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ hL hU).1 (Subsingleton.elim _ _)

/-- **`f_* 𝒪 = 𝒪` for a morphism to the spectrum of a field with invariant global sections.**
The spectrum of a field has a one-point space, so an isomorphism on global sections is an
isomorphism of sheaves: the only other open is the empty one, where both sides vanish. -/
theorem isIso_c_of_isIso_appTop_spec (E : Type u) [Field E] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of E)) (hf : IsIso ((Scheme.ΓSpecIso (.of E)).inv ≫ f.appTop)) :
    IsIso f.toLRSHom.toHom.c := by
  have := hf
  have h : IsIso f.appTop := IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of E)).inv f.appTop
  exact (Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_iff_bijective_appTop f).2
    (ConcreteCategory.bijective_of_isIso f.appTop)

/-! ### The rational point induced on a base change -/

section RationalPoint

variable {k K : Type u} [Field k] [Field K] [Algebra k K] (X : Over (Spec (.of k)))
  (pt : Spec (.of k) ⟶ X.left) (hpt : pt ≫ X.hom = 𝟙 (Spec (.of k)))

/-- **The `K`-rational point of the base change induced by a `k`-rational point.** It is the
given point in the `X`-coordinate and the identity in the `Spec K` coordinate, so it is a
section of the structure morphism `X_K ⟶ Spec K`. -/
def baseChangePoint : Spec (.of K) ⟶ SchemeOver.baseChange k K X :=
  pullback.lift (spectrumMap k K ≫ pt) (𝟙 (Spec (.of K)))
    (by rw [Category.assoc, hpt, Category.comp_id, Category.id_comp])

/-- The `X`-coordinate of the induced point is the given point composed with `Spec K ⟶ Spec k`. -/
@[simp]
lemma baseChangePoint_comp_fst :
    baseChangePoint X pt hpt ≫ pullback.fst X.hom (spectrumMap k K) = spectrumMap k K ≫ pt :=
  pullback.lift_fst _ _ _

/-- The induced point is a section of the structure morphism of the base change. -/
@[simp]
lemma baseChangePoint_comp_snd :
    baseChangePoint X pt hpt ≫ pullback.snd X.hom (spectrumMap k K) = 𝟙 (Spec (.of K)) :=
  pullback.lift_snd _ _ _

/-- **The induced point is equivariant**: the twist `id_X × Spec(σ)` moves it by `Spec σ`. This
is what makes the normalisation of a family of isomorphisms at the point compatible with the
Galois action. -/
lemma baseChangePoint_comp_galoisTwist (σ : K ≃ₐ[k] K) :
    baseChangePoint X pt hpt ≫ galoisTwist k K X σ =
      specMapAlgAut k K σ ≫ baseChangePoint X pt hpt := by
  apply pullback.hom_ext
  · rw [Category.assoc, galoisTwist_comp_fst, baseChangePoint_comp_fst, Category.assoc,
      baseChangePoint_comp_fst, ← Category.assoc, specMapAlgAut_comp_structureMap]
  · rw [Category.assoc, galoisTwist_comp_snd, ← Category.assoc, baseChangePoint_comp_snd,
      Category.id_comp, Category.assoc, baseChangePoint_comp_snd, Category.comp_id]

end RationalPoint

/-- The pullback of an invertible module along a morphism of schemes is invertible. -/
private theorem isInvertible_pullback_obj {Y Z : Scheme.{u}} (g : Y ⟶ Z) (M : Z.Modules)
    (hM : Stacks.SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 M) :
    Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      ((Scheme.Modules.pullback g).obj M) :=
  Stacks.RingedSpace.modulePullback_isInvertible_of g.toLRSHom.toShHom _ hM

/-- If the pullback of a Picard class along an endomorphism `g` of the scheme is the class
again, then the chosen representative is isomorphic to its own pullback along `g`. Pullback of
classes is defined on the chosen representative, so this is
`Stacks.SheafOfModules.picardClass_eq_iff` with nothing in between. -/
lemma nonempty_iso_pullback_of_schemePullbackClass_eq {Y : Scheme.{u}} (g : Y ⟶ Y)
    (x : ofScheme Y) (hx : schemePullbackClass g x = x) :
    Nonempty ((picardRepresentative Y.toRingedSpace x).obj ≅
      (Scheme.Modules.pullback g).obj (picardRepresentative Y.toRingedSpace x).obj) :=
  (picardClass_eq_iff Y.presheaf (structureIsSheaf Y.toRingedSpace) _ _
      (picardRepresentative Y.toRingedSpace x).property
      (isInvertible_pullback_obj g _ (picardRepresentative Y.toRingedSpace x).property)).1
    ((classOf_picardRepresentative Y.toRingedSpace x).trans hx.symm)

/-! ### Descent of a Galois-fixed class along a finite Galois extension -/

section Descent

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
  (X : Over (Spec (.of k)))

/-- **An invertible module on a finite Galois base change isomorphic to each of its twists is
pulled back from the base.** Let `K/k` be a finite Galois extension, let `X` be a scheme over
`k` with `H⁰(X_K, 𝒪) = K` and a `k`-rational point, and let `L` be an invertible module on `X_K`
admitting, for every `σ ∈ Gal(K/k)`, *some* isomorphism `L ≅ f_σ^* L`. Then `L` is the pullback
of an invertible module on `X`.

The hypothesis gives each `σ` an isomorphism separately and nothing pins the family down to a
cocycle. The rational point does: `Pic(Spec K) = 0` trivialises the restriction of `L` to it
(`Stacks.Picard.nonempty_iso_unitModule_spec`), the structure morphism `X_K ⟶ Spec K` has
invariant structure sheaf (`Stacks.Picard.isIso_c_of_isIso_appTop_spec`), so an isomorphism of
invertible modules on `X_K` is determined by its restriction along the point
(`Stacks.Picard.existsUnique_sectionPullback_mapIso`), and the family normalised against the
trivialisation is a cocycle by `Stacks.Picard.twistNormalizedIso_mul`. That cocycle is a Galois
descent datum, and Tag 0CDR in its invertible form
(`Stacks.Descent.exists_isInvertible_pullback_iso_of_galoisDescentData_baseChange`) descends
it. -/
theorem exists_isInvertible_pullback_iso_of_forall_nonempty_iso_galoisTwist
    (hΓ : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫
      (pullback.snd X.hom (spectrumMap k K)).appTop))
    (pt : Spec (.of k) ⟶ X.left) (hpt : pt ≫ X.hom = 𝟙 (Spec (.of k)))
    (L : (SchemeOver.baseChange k K X).Modules)
    (hL : Stacks.SheafOfModules.IsInvertible (SchemeOver.baseChange k K X).presheaf
      (SchemeOver.baseChange k K X).ringCatSheaf.2 L)
    (hiso : ∀ σ : K ≃ₐ[k] K,
      Nonempty (L ≅ (Scheme.Modules.pullback (galoisTwist k K X σ)).obj L)) :
    ∃ N : X.left.Modules,
      Stacks.SheafOfModules.IsInvertible X.left.presheaf X.left.ringCatSheaf.2 N ∧
        Nonempty ((Scheme.Modules.pullback
          (pullback.fst X.hom (spectrumMap k K))).obj N ≅ L) := by
  classical
  have hs := baseChangePoint_comp_snd (K := K) X pt hpt
  have hc : IsIso (pullback.snd X.hom (spectrumMap k K)).toLRSHom.toHom.c :=
    isIso_c_of_isIso_appTop_spec K _ hΓ
  have hLinst : Stacks.SheafOfModules.IsInvertible
      (pullback X.hom (spectrumMap k K)).presheaf
      (pullback X.hom (spectrumMap k K)).ringCatSheaf.2 L := hL
  -- the trivialisation of the restriction to the rational point
  obtain ⟨t⟩ := nonempty_iso_unitModule_spec K
    ((Scheme.Modules.pullback (baseChangePoint X pt hpt)).obj L)
    (isInvertible_pullback_obj _ _ hL)
  -- the family normalised at the point, and its uniqueness
  have hnorm : ∀ σ : K ≃ₐ[k] K, ∃!
      b : L ≅ (Scheme.Modules.pullback (galoisTwist k K X σ)).obj L,
      (Scheme.Modules.pullback (baseChangePoint X pt hpt)).mapIso b =
        twistNormalizedIso (baseChangePoint X pt hpt) (galoisTwist k K X σ)
          (specMapAlgAut k K σ) (baseChangePoint X pt hpt ≫ galoisTwist k K X σ) rfl
          (baseChangePoint_comp_galoisTwist X pt hpt σ).symm L t := by
    intro σ
    have : Stacks.SheafOfModules.IsInvertible
        (pullback X.hom (spectrumMap k K)).presheaf
        (pullback X.hom (spectrumMap k K)).ringCatSheaf.2
        ((Scheme.Modules.pullback (galoisTwist k K X σ)).obj L) :=
      isInvertible_pullback_obj _ _ hL
    obtain ⟨e⟩ := hiso σ
    exact existsUnique_sectionPullback_mapIso (pullback.snd X.hom (spectrumMap k K))
      (baseChangePoint X pt hpt) hs _ _ e _
  choose φ hφ hφuniq using hnorm
  -- the normalised family is a Galois descent datum
  let A : Stacks.Descent.GaloisDescentData (K ≃ₐ[k] K)
      (Stacks.Descent.baseChangeProjection k K X)
      (Stacks.Descent.baseChangeOverAction k K X) :=
    { module := L
      isQuasicoherent := isQuasicoherent_of_isInvertible _ hL
      φ := φ
      cocycle := fun σ τ => (hφuniq (σ * τ) _
        (twistNormalizedIso_mul (baseChangePoint X pt hpt) (galoisTwist k K X σ)
          (galoisTwist k K X τ) (galoisTwist k K X (σ * τ)) (specMapAlgAut k K σ)
          (specMapAlgAut k K τ) (specMapAlgAut k K (σ * τ))
          (baseChangePoint X pt hpt ≫ galoisTwist k K X σ)
          (baseChangePoint X pt hpt ≫ galoisTwist k K X τ)
          (baseChangePoint X pt hpt ≫ galoisTwist k K X (σ * τ))
          (galoisTwist_mul k K X σ τ).symm (specMapAlgAut_mul k K σ τ).symm rfl
          (baseChangePoint_comp_galoisTwist X pt hpt σ).symm rfl
          (baseChangePoint_comp_galoisTwist X pt hpt τ).symm rfl
          (baseChangePoint_comp_galoisTwist X pt hpt (σ * τ)).symm L t (φ σ) (φ τ)
          (hφ σ) (hφ τ))).symm }
  obtain ⟨N, -, hNinv, ⟨e⟩⟩ :=
    Stacks.Descent.exists_isInvertible_pullback_iso_of_galoisDescentData_baseChange k K X A hL
  exact ⟨N, hNinv, ⟨e⟩⟩

/-- **A Galois-fixed Picard class of a finite Galois base change is pulled back from the
base.** The module statement
`Stacks.Picard.exists_isInvertible_pullback_iso_of_forall_nonempty_iso_galoisTwist`, read on the
chosen representative of the class. -/
theorem exists_schemePullbackClass_eq_of_galoisFixed
    (hΓ : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫
      (pullback.snd X.hom (spectrumMap k K)).appTop))
    (pt : Spec (.of k) ⟶ X.left) (hpt : pt ≫ X.hom = 𝟙 (Spec (.of k)))
    (y : ofScheme (SchemeOver.baseChange k K X)) (hy : y ∈ galoisFixedClasses k K X) :
    ∃ x : ofScheme X.left,
      schemePullbackClass (pullback.fst X.hom (spectrumMap k K)) x = y := by
  obtain ⟨N, hNinv, ⟨e⟩⟩ :=
    exists_isInvertible_pullback_iso_of_forall_nonempty_iso_galoisTwist X hΓ pt hpt
      (picardRepresentative (SchemeOver.baseChange k K X).toRingedSpace y).obj
      (picardRepresentative (SchemeOver.baseChange k K X).toRingedSpace y).property
      fun σ => nonempty_iso_pullback_of_schemePullbackClass_eq (galoisTwist k K X σ) y (hy σ)
  exact ⟨picardClass X.left.presheaf (structureIsSheaf X.left.toRingedSpace) N hNinv,
    (eq_schemePullbackClass_classOf (pullback.fst X.hom (spectrumMap k K)) y N hNinv e.symm).symm⟩

end Descent

end Stacks.Picard

end
