module

public import StacksFrontier.AlgebraicGeometry.Duality.CurveFamilyDualizingSheafInvertible
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.BaseChange
public import StacksFrontier.AlgebraicGeometry.AmpleFibreLimit.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.RelativeAmpleFpqcLocalOnBaseFull
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleAffineBase.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower

/-!
# The locus of fibres with ample dualizing sheaf in a family of Gorenstein curves is open

Let `S` be Noetherian and `f : X ⟶ S` proper, flat and Cohen–Macaulay with one-dimensional fibres,
whose fibres over field-valued points all have invertible dualizing sheaf. There is an open
`U ⊆ S` such that a field-valued point `Spec K ⟶ S` lands in `U` exactly when the dualizing sheaf
of the fibre `X_K` is ample. This is the openness assertion in the proof of Stacks 0E74, for a
family whose total space is a scheme.

The relative dualizing sheaf `ω_{X/S}` is invertible
(`Stacks.Duality.isInvertibleModule_relativeDualizingSheaf`) and restricts to `ω_{X_K}` on every
fibre (`Stacks.Duality.nonempty_pullback_relativeDualizingSheaf_iso`). `U` is the union of the
opens over which `ω_{X/S}` is relatively ample. A point of `U` has ample fibre dualizing sheaf by
base change of relative ampleness ([Stacks, Tag 0893]) and [Stacks, Tag 01VK]; conversely an ample
dualizing sheaf on `X_K` descends to the fibre over the residue field ([Stacks, Tag 0D2P]) and
spreads to a neighbourhood ([Stacks, Tag 0D2S]).

## Main results

* `Stacks.Duality.exists_opens_forall_mem_iff_isAmple_dualizingSheafOverField`.

## References

* [Stacks Project, Tag 0E74](https://stacks.math.columbia.edu/tag/0E74)
* [Stacks Project, Tag 0D2S](https://stacks.math.columbia.edu/tag/0D2S)
* [Stacks Project, Tag 0D2P](https://stacks.math.columbia.edu/tag/0D2P)
* [Stacks Project, Tag 0893](https://stacks.math.columbia.edu/tag/0893)
* [Stacks Project, Tag 01VK](https://stacks.math.columbia.edu/tag/01VK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AmpleLocallyClosed (pullbackModule)

universe u

namespace Stacks.Duality

variable {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsProper f] [Flat f]

omit [AlgebraicGeometry.IsNoetherian S] [IsProper f] [Flat f] in
/-- A family relatively ample over an open `V` has ample base change to every field-valued point
of `V`. -/
private theorem isAmple_pullbackModule_of_isRelativelyAmple_restrict (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {V : S.Opens}
    (hV : Stacks.RelativeAmple.IsRelativelyAmple (f ∣_ V) (pullbackModule (f ⁻¹ᵁ V).ι L))
    {K : Type u} [Field K] {X' : Scheme.{u}} {y : Spec (CommRingCat.of K) ⟶ S} {g' : X' ⟶ X}
    {f' : X' ⟶ Spec (CommRingCat.of K)} (sq : IsPullback g' f' f y)
    (ht : y (IsLocalRing.closedPoint K) ∈ V) :
    Stacks.Ample.IsAmple X' (pullbackModule g' L) := by
  have hrange : Set.range y.base ⊆ Set.range V.ι.base := by
    rintro _ ⟨z, rfl⟩
    rwa [Subsingleton.elim z (IsLocalRing.closedPoint K), V.range_ι]
  let y' := IsOpenImmersion.lift V.ι y hrange
  have hy' : y' ≫ V.ι = y := IsOpenImmersion.lift_fac _ _ _
  have hR := (isPullback_morphismRestrict f V).flip
  let g'' : X' ⟶ f ⁻¹ᵁ V := hR.lift g' (f' ≫ y') (by rw [Category.assoc, hy', sq.w])
  have hg'' : g'' ≫ (f ⁻¹ᵁ V).ι = g' := hR.lift_fst _ _ _
  have hleft : IsPullback g'' f' (f ∣_ V) y' := by
    refine IsPullback.of_right ?_ (hR.lift_snd _ _ _) hR
    rwa [hg'', hy']
  have hamp := (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple f' _).mp
    (Stacks.AmpleBridge.isRelativelyAmple_pullbackModule_of_isPullback hleft
      (pullbackModule (f ⁻¹ᵁ V).ι L) hV)
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _
    ((Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso g'' (f ⁻¹ᵁ V).ι L).symm ≪≫
      Stacks.RelativeAmpleBaseChange.pullbackModuleCongr hg'' L)).mp hamp

omit [AlgebraicGeometry.IsNoetherian S] [Flat f] in
/-- An invertible module whose base change to a field-valued point `y` of `S` is ample is
relatively ample over an open neighbourhood of the image of `y`. -/
private theorem exists_mem_isRelativelyAmple_of_isAmple_pullbackModule (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {K : Type u} [Field K] {X' : Scheme.{u}}
    {y : Spec (CommRingCat.of K) ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ Spec (CommRingCat.of K)}
    (sq : IsPullback g' f' f y) (hamp : Stacks.Ample.IsAmple X' (pullbackModule g' L)) :
    ∃ V : S.Opens, y (IsLocalRing.closedPoint K) ∈ V ∧
      Stacks.RelativeAmple.IsRelativelyAmple (f ∣_ V) (pullbackModule (f ⁻¹ᵁ V).ι L) := by
  let t := y (IsLocalRing.closedPoint K)
  let φ := S.descResidueField (Scheme.stalkClosedPointTo y)
  have hy : Spec.map φ ≫ S.fromSpecResidueField t = y :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K S y
  have hF := IsPullback.of_hasPullback f (S.fromSpecResidueField t)
  let a : X' ⟶ f.fiber t := hF.lift g' (f' ≫ Spec.map φ) (by rw [Category.assoc, hy, sq.w])
  have ha : a ≫ f.fiberι t = g' := hF.lift_fst _ _ _
  have hleft : IsPullback a f' (f.fiberToSpecResidueField t) (Spec.map φ) := by
    refine IsPullback.of_right ?_ (hF.lift_snd _ _ _) hF
    show IsPullback (a ≫ f.fiberι t) f' f (Spec.map φ ≫ S.fromSpecResidueField t)
    rwa [ha, hy]
  have hrelK : Stacks.RelativeAmple.IsRelativelyAmple f'
      (pullbackModule a (pullbackModule (f.fiberι t) L)) :=
    (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple f' _).mpr
      ((Stacks.RelativeVeryAmple.isAmple_congr _ _
        ((Stacks.RelativeAmpleBaseChange.pullbackModuleCongr ha L).symm ≪≫
          Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso a (f.fiberι t) L)).mp hamp)
  have : Flat (Spec.map φ) := Flat.SpecMap_iff.mpr (RingHom.Flat.of_isField (Field.toIsField _) _)
  have : Surjective (Spec.map φ) := ⟨fun _ => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
  have hcov : Presieve.ofArrows (fun _ : PUnit.{u + 1} => Spec (CommRingCat.of K))
      (fun _ => Spec.map φ) ∈ Scheme.fpqcPrecoverage (Spec (S.residueField t)) := by
    rw [Presieve.ofArrows_pUnit]
    exact (Spec.map φ).singleton_mem_fpqcPrecoverage
  have hrelt := (Stacks.Descent.isRelativelyAmple_iff_forall_of_fpqcCover hcov
    (f.fiberToSpecResidueField t) (pullbackModule (f.fiberι t) L)
    (fun _ => hleft)).mpr (fun _ => hrelK)
  exact Stacks.AmpleFibreLimit.exists_mem_isRelativelyAmple_of_isAmple_fibre f L t
    ((Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple _ _).mp hrelt)

/-- **The ample locus of the fibre dualizing sheaves is open.** For `f : X ⟶ S` proper, flat and
Cohen–Macaulay with one-dimensional fibres over a Noetherian scheme, all of whose fibres over
field-valued points have invertible dualizing sheaf, there is an open `U ⊆ S` such that a
field-valued point `y : Spec K ⟶ S` lies in `U` exactly when the dualizing sheaf `ω_{X_K}` of the
fibre `X_K = X ×_S Spec K` is ample. -/
theorem exists_opens_forall_mem_iff_isAmple_dualizingSheafOverField
    (hCM : f.IsCohenMacaulay (isLocallyNoetherian_fiber_left (ftsHomToBase f)))
    (hd : ∀ x : X, topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = ((1 : ℕ) : WithBot ℕ∞))
    (hfib : ∀ (K : Type u) [Field K] (X' : Scheme.{u}) (y : Spec (CommRingCat.of K) ⟶ S)
      (g' : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of K)) [IsProper f'], IsPullback g' f' f y →
        SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2 (dualizingSheafOverField f')) :
    ∃ U : S.Opens, ∀ (K : Type u) [Field K] (X' : Scheme.{u}) (y : Spec (CommRingCat.of K) ⟶ S)
      (g' : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of K)) [IsProper f']
      (sq : IsPullback g' f' f y),
      letI := hfib K X' y g' f' sq
      (y (IsLocalRing.closedPoint K) ∈ U ↔
        Stacks.Ample.IsAmple X' (dualizingSheafOverField f')) := by
  let L : X.Modules :=
    relativeDualizingSheaf (ftsHomToBase f) (properCompactification (ftsHomToBase f)) 1
  have : Stacks.Ample.IsInvertibleModule X L :=
    isInvertibleModule_relativeDualizingSheaf f hCM hd hfib
  let 𝒱 : Set S.Opens :=
    {V | Stacks.RelativeAmple.IsRelativelyAmple (f ∣_ V) (pullbackModule (f ⁻¹ᵁ V).ι L)}
  refine ⟨sSup 𝒱, fun K _ X' y g' f' _ sq => ?_⟩
  let := hfib K X' y g' f' sq
  obtain ⟨e⟩ := nonempty_pullback_relativeDualizingSheaf_iso f hCM hd sq
  let e' : pullbackModule g' L ≅ dualizingSheafOverField f' := e
  rw [← Stacks.RelativeVeryAmple.isAmple_congr _ _ e']
  constructor
  · intro ht
    obtain ⟨V, hV, htV⟩ := TopologicalSpace.Opens.mem_sSup.mp ht
    exact isAmple_pullbackModule_of_isRelativelyAmple_restrict f L (V := V) hV sq htV
  · intro hamp
    obtain ⟨V, htV, hV⟩ := exists_mem_isRelativelyAmple_of_isAmple_pullbackModule f L sq hamp
    exact TopologicalSpace.Opens.mem_sSup.mpr ⟨V, hV, htV⟩

end Stacks.Duality

end
