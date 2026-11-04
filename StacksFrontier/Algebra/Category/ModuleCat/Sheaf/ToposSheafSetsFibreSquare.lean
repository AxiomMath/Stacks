module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposTerminalSections

/-!
# A sectionwise fibre of sheaves of sets is a pullback square

Let `g : A ⟶ B` be a morphism of sheaves of sets on a site and let `z : ⊤ ⟶ B` be a global
section of `B`. A morphism `k : M ⟶ A` which is, section by section, a bijection onto the fibre
of `g` over `z` exhibits `M` as the pullback of `g` along `z`.

This is the input the kernel transport of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposRingInverseImageKernel` asks for: there the
square is assumed and carried along a left exact functor, and here it is produced from the
sectionwise description a defining ideal of a thickening comes with.

## Main results

* `Stacks.Sheaves.ToposPullback.isPullback_terminal_of_sections`: sectionwise injectivity
  together with sectionwise surjectivity onto the fibre gives the pullback square.

## Implementation notes

The lift out of a competing cone is built section by section from the surjectivity hypothesis,
with a choice; it is natural because `k` is sectionwise injective and both `k` and the cone leg
are natural, so the two candidate values have the same image in `A`. Uniqueness of the lift is
again sectionwise injectivity, and the compatibility with the leg into the terminal sheaf is
automatic.

The limit is produced as a `CategoryTheory.Limits.PullbackCone`, not by comparing with a chosen
pullback, so no existence of pullbacks in the category of sheaves of sets is required.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite

namespace Stacks.Sheaves.ToposPullback

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- **A sectionwise bijection onto the fibre over a global section is a pullback square.** If
`k : M ⟶ A` is injective on sections and its sections over every object of the site are exactly
the sections of `A` carried by `g` to the global section `z`, then `M` is the pullback of `g`
along `z`. -/
theorem isPullback_terminal_of_sections {M A B : Sheaf J (Type w)} (k : M ⟶ A) (g : A ⟶ B)
    (z : ⊤_ (Sheaf J (Type w)) ⟶ B) (hcomm : k ≫ g = terminal.from M ≫ z)
    (hinj : ∀ (U : Cᵒᵖ) (m m' : M.obj.obj U), k.hom.app U m = k.hom.app U m' → m = m')
    (hsurj : ∀ (U : Cᵒᵖ) (a : A.obj.obj U),
      g.hom.app U a = z.hom.app U (Sheaf.terminalSheafSection J U) →
        ∃ m : M.obj.obj U, k.hom.app U m = a) :
    IsPullback k (terminal.from M) g z := by
  classical
  have key : ∀ (s : PullbackCone g z) (U : Cᵒᵖ) (x : s.pt.obj.obj U),
      ∃ m : M.obj.obj U, k.hom.app U m = s.fst.hom.app U x := by
    intro s U x
    refine hsurj U _ ?_
    have h : g.hom.app U (s.fst.hom.app U x) = z.hom.app U (s.snd.hom.app U x) :=
      congrArg (fun q : s.pt ⟶ B ↦ q.hom.app U x) s.condition
    exact h.trans (congrArg (z.hom.app U) (Sheaf.eq_terminalSheafSection _))
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hcomm
    (fun s ↦ ⟨{ app := fun U ↦ ↾fun x ↦ (key s U x).choose
                naturality := by
                  intro U V p
                  ext x
                  dsimp
                  refine hinj V _ _ ?_
                  rw [(key s V (s.pt.obj.map p x)).choose_spec,
                    NatTrans.naturality_apply k.hom p ((key s U x).choose),
                    (key s U x).choose_spec, NatTrans.naturality_apply s.fst.hom p x] }⟩)
    (fun s ↦ ?_) (fun s ↦ Subsingleton.elim (α := s.pt ⟶ ⊤_ (Sheaf J (Type w))) _ _)
    (fun s m hfst _ ↦ ?_))
  · refine Sheaf.hom_ext_sections fun U x ↦ ?_
    change k.hom.app U ((key s U x).choose) = s.fst.hom.app U x
    exact (key s U x).choose_spec
  · refine Sheaf.hom_ext_sections fun U x ↦ ?_
    change m.hom.app U x = (key s U x).choose
    refine hinj U _ _ ?_
    rw [(key s U x).choose_spec]
    exact congrArg (fun q : s.pt ⟶ A ↦ q.hom.app U x) hfst

end Stacks.Sheaves.ToposPullback

end
