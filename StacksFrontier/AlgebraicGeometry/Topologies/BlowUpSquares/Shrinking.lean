module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.LocallyPrincipalPullback.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AlmostBlowUp.IsomorphismAwayFromCenter

/-!
# Shrinking the modification of an almost blowup square

Let `I` be a quasi-coherent ideal sheaf on `X` and let `b : X' ⟶ X` be the modification of an
almost blowup square with centre `I`. A finitely presented closed subscheme `W ⊆ X'`, cut out
by `J`, contains the complement of the exceptional subscheme exactly when `J` is contained in
the ideal of sections supported on that subscheme, and that in turn happens exactly when `W`,
with the inverse image of the centre, is again an almost blowup square for `I`.

The first equivalence is `AlgebraicGeometry.isIso_restrict_iff_le_supportedSectionsIdeal`, which
needs neither finite presentation nor an almost blowup square; the second is
`AlgebraicGeometry.le_supportedSectionsIdeal_iff_isAlmostBlowUpSquare`.

## Main results

* `AlgebraicGeometry.le_ker_iff_comap_eq_bot`: an ideal sheaf is contained in the kernel of a
  morphism exactly when its inverse image along that morphism vanishes.
* `AlgebraicGeometry.supportedSectionsIdeal_map_of_restrict_isIso`: a morphism that is an
  isomorphism away from a closed subset carries the ideal of sections supported on the preimage
  of that subset onto the ideal of sections supported on the subset itself.
* `AlgebraicGeometry.le_supportedSectionsIdeal_iff_isAlmostBlowUpSquare`: containing the blowup
  is equivalent to being again the modification of an almost blowup square.

## Implementation notes

Both ideals in `AlgebraicGeometry.supportedSectionsIdeal_map_of_restrict_isIso` are kernels of
the inclusions of the open complements, by
`AlgebraicGeometry.supportedSectionsIdeal_eq_complementKernel`, and the two inclusions differ by
the restriction of the morphism over the complement, so the pushforward is a kernel that may be
cancelled against an isomorphism.

In `AlgebraicGeometry.le_supportedSectionsIdeal_iff_isAlmostBlowUpSquare` the blowup
identification for the smaller square is obtained from the one for the given square: the ideal
of supported sections of the smaller modification pushes forward to that of the given one, so the
two closed subschemes they cut out have the same kernel over `X'` and are therefore identified
over `X`. The converse direction only needs that both modifications are isomorphisms away from
the centre, which forces the inclusion of the smaller one to be an isomorphism there too.

## References

* [Stacks Project, Tag 0EV8](https://stacks.math.columbia.edu/tag/0EV8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- An ideal sheaf is contained in the kernel of a morphism exactly when its inverse image along
that morphism is the zero ideal. -/
public theorem le_ker_iff_comap_eq_bot {X Y : Scheme.{u}} (J : X.IdealSheafData) (f : Y ⟶ X) :
    J ≤ f.ker ↔ J.comap f = ⊥ := by
  rw [← Scheme.IdealSheafData.map_bot f, Scheme.IdealSheafData.le_map_iff_comap_le, le_bot_iff]

/-- The inverse image of the kernel of a morphism along that same morphism vanishes. -/
public theorem ker_comap_self {X Y : Scheme.{u}} (f : Y ⟶ X) : f.ker.comap f = ⊥ :=
  (le_ker_iff_comap_eq_bot f.ker f).mp le_rfl

/-- Pushing an ideal sheaf forward along a closed immersion identifies the closed subscheme it
cuts out with the closed subscheme of the pushforward, as schemes over the target. -/
public def idealMapSubschemeIso {P Q : Scheme.{u}} (f : Q ⟶ P) [IsClosedImmersion f]
    (K : Q.IdealSheafData) (L : P.IdealSheafData) (hmap : K.map f = L) :
    Over.mk L.subschemeι ≅ Over.mk (K.subschemeι ≫ f) := by
  have hker : (K.subschemeι ≫ f).ker = L := by
    rw [Scheme.Hom.ker_comp, K.ker_subschemeι, hmap]
  let m : L.subscheme ⟶ K.subscheme :=
    IsClosedImmersion.lift (K.subschemeι ≫ f) L.subschemeι
      (by rw [hker, Scheme.IdealSheafData.ker_subschemeι])
  have hmfac : m ≫ (K.subschemeι ≫ f) = L.subschemeι := IsClosedImmersion.lift_fac _ _ _
  have hm : IsIso m :=
    IsClosedImmersion.isIso_of_ker_eq L.subschemeι (K.subschemeι ≫ f) m hmfac
      (by rw [hker, Scheme.IdealSheafData.ker_subschemeι])
  exact Over.isoMk (asIso m) hmfac

/-- A morphism which is an isomorphism over the complement of a closed subset carries the ideal
of sections supported on the preimage of that subset onto the ideal of sections supported on the
subset. -/
public theorem supportedSectionsIdeal_map_of_restrict_isIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    (Z : Set X) (hZ : IsClosed Z)
    (hf : IsIso (f ∣_ (⟨Zᶜ, hZ.isOpen_compl⟩ : X.Opens))) :
    (supportedSectionsIdeal (f.base ⁻¹' Z)).map f = supportedSectionsIdeal Z := by
  let U : X.Opens := ⟨Zᶜ, hZ.isOpen_compl⟩
  let W : Y.Opens := ⟨(f.base ⁻¹' Z)ᶜ, (hZ.preimage f.continuous).isOpen_compl⟩
  have hWU : W = f ⁻¹ᵁ U := by
    ext x
    simp [W, U, Set.preimage_compl]
  have hcomp : W.ι ≫ f = (f ∣_ U) ≫ U.ι := by
    cases hWU
    exact (morphismRestrict_ι f U).symm
  have hWker : supportedSectionsIdeal (f.base ⁻¹' Z) = W.ι.ker :=
    supportedSectionsIdeal_eq_complementKernel (f.base ⁻¹' Z) (hZ.preimage f.continuous)
  have hUker : supportedSectionsIdeal Z = U.ι.ker :=
    supportedSectionsIdeal_eq_complementKernel Z hZ
  have : IsIso (f ∣_ U) := hf
  rw [hWker, hUker]
  calc
    (W.ι.ker).map f = (W.ι ≫ f).ker := Scheme.IdealSheafData.map_ker _ _
    _ = ((f ∣_ U) ≫ U.ι).ker := by
      rw [hcomp]
      rfl
    _ = U.ι.ker := Scheme.Hom.ker_comp_of_isIso (f ∣_ U) U.ι

/-- **Stacks Project, Tag 0EV8.** For a finitely presented closed subscheme of the modification
of an almost blowup square, containing the blowup of the centre is equivalent to the induced
square, with the scheme-theoretic inverse image of the centre, being again an almost blowup
square. -/
@[stacks 0EV8 "(2) iff (3)"]
public theorem le_supportedSectionsIdeal_iff_isAlmostBlowUpSquare {X X' : Scheme.{u}}
    (I : X.IdealSheafData) (b : X' ⟶ X) (h : IsAlmostBlowUpSquare I b)
    (J : X'.IdealSheafData) (hJ : FinitePresentation J.subschemeι) :
    J ≤ supportedSectionsIdeal (I.comap b).support ↔
      IsAlmostBlowUpSquare I (J.subschemeι ≫ b) := by
  let f := J.subschemeι
  let E := (I.comap b).support
  let U : X'.Opens := ⟨(E : Set X')ᶜ, E.isClosed.isOpen_compl⟩
  have key : J ≤ supportedSectionsIdeal (E : Set X') ↔ IsIso (f ∣_ U) := by
    rw [supportedSectionsIdeal_eq_complementKernel (E : Set X') E.isClosed,
      le_ker_iff_comap_eq_bot, restrict_isIso_iff_comap_bot]
  constructor
  · intro hJK
    have hfIso : IsIso (f ∣_ U) := key.1 hJK
    refine ⟨h.center_finitePresentation, ?_, ?_, ?_, ?_⟩
    · rw [Scheme.IdealSheafData.comap_comp]
      exact Stacks.Divisors.isLocallyPrincipal_comap f (I.comap b)
        h.exceptional_locallyPrincipal
    · have : IsProper b := h.proper
      infer_instance
    · have := hJ.locallyOfFinitePresentation
      have := hJ.quasiCompact
      have := hJ.quasiSeparated
      have := h.finitePresentation.locallyOfFinitePresentation
      have := h.finitePresentation.quasiCompact
      have := h.finitePresentation.quasiSeparated
      exact ⟨inferInstance, inferInstance, inferInstance⟩
    · let K := supportedSectionsIdeal (E : Set X')
      let L := supportedSectionsIdeal ((I.comap (f ≫ b)).support : Set J.subscheme)
      have hmap : L.map f = K := by
        have h' := supportedSectionsIdeal_map_of_restrict_isIso f (E : Set X') E.isClosed hfIso
        simpa [L, K, E, Scheme.IdealSheafData.support_comap,
          Scheme.IdealSheafData.comap_comp] using h'
      let e0 : Over.mk K.subschemeι ≅ Over.mk (L.subschemeι ≫ f) :=
        idealMapSubschemeIso f L K hmap
      let e : Over.mk (K.subschemeι ≫ b) ≅ Over.mk (L.subschemeι ≫ f ≫ b) :=
        Over.isoMk ((Over.forget X').mapIso e0)
          (by simpa [Category.assoc] using congrArg (fun g => g ≫ b) (Over.w e0.hom))
      exact ⟨e.symm ≪≫ h.blowUp.some⟩
  · intro hnew
    let V : X.Opens := ⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩
    have hV : b ⁻¹ᵁ V = U := by
      ext x
      simp [V, U, E, Scheme.IdealSheafData.support_comap]
    have : IsIso (b ∣_ V) := isIso_restrict_compl_support I b h
    have : IsIso ((f ≫ b) ∣_ V) := isIso_restrict_compl_support I (f ≫ b) hnew
    have hfIsoPre : IsIso (f ∣_ (b ⁻¹ᵁ V)) := by
      have hcancel : IsIso (((f ≫ b) ∣_ V) ≫ inv (b ∣_ V)) := inferInstance
      have heq : ((f ≫ b) ∣_ V) ≫ inv (b ∣_ V) = f ∣_ (b ⁻¹ᵁ V) := by
        rw [morphismRestrict_comp]
        simp
      exact heq ▸ hcancel
    exact key.2 (by rw [← hV]; exact hfIsoPre)

end AlgebraicGeometry

end
