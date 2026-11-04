module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardEssentialImageDirect.Criterion
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPointPushforward
public import Mathlib.CategoryTheory.Adjunction.Comma
public import Mathlib.CategoryTheory.Limits.ExactFunctor
import StacksCore.Tactic.StacksAttribute

/-!
# Exactness of the direct image of modules along a closed immersion of ringed topoi

Let `i : (Sh(C), O) ⟶ (Sh(D), O')` be a closed immersion of ringed topoi with locally surjective
structure map. Stacks 08M3 asserts, among other things, that the direct image
`i_* : Mod(O) ⥤ Mod(O')` is exact. This file proves it.

Left exactness is immediate from the construction: the underlying sheaf of sets of `i_*F` is the
direct image of the underlying sheaf of sets of `F`, the direct image of sheaves of sets is a right
adjoint, and the underlying-sheaf functor on sheaves of modules both preserves and reflects finite
limits. Right exactness is not: it comes from `i_*` being a *left* adjoint, which is the
consequence of the other two assertions of Stacks 08M3. Being fully faithful with essential image
the `I`-annihilated modules, `i_*` has a right adjoint sending an `O'`-module `G` to the largest
submodule of `G` annihilated by `I`.

## Main definitions

* `Stacks.SheafOfModules.annihilatorSubmodule`: for an ideal subsheaf `I` of a sheaf of rings `R`
  with commuting sections and a sheaf of `R`-modules `M`, the subsheaf of sections all of whose
  restrictions are annihilated by `I`. It is the largest subsheaf of `M` annihilated by `I`.
* `AlgebraicGeometry.ClosedRingedImmersion.sourceRingSheaf`: the sheaf of rings underlying the
  structure sheaf of the source, mirroring the existing `.targetRingSheaf`.

## Main results

* `Stacks.SheafOfModules.smul_annihilatorSubmodule_eq_zero`: `I` annihilates
  `annihilatorSubmodule`.
* `Stacks.SheafOfModules.annihilatorLift` and `.annihilatorLift_comp_ι`: a morphism into `M` from
  a module annihilated by `I` factors through `annihilatorSubmodule`.
* `Stacks.SheafOfModules.isLeftAdjoint_of_essImage_eq_annihilated`: a fully faithful functor into
  sheaves of `R`-modules whose essential image is exactly the `I`-annihilated modules is a left
  adjoint.
* `AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_exact`: **Stacks 08M3**, the
  exactness assertion.

## Implementation notes

The annihilator is a *subsheaf*, so its sections over `U` cannot be taken to be the sections of `M`
over `U` killed by `I(U)`: that is not stable under restriction in a useful way. They are the
sections all of whose restrictions are killed, which is the standard "ideal transporter" and is
stable under restriction by construction and a subsheaf because `M` is separated.

Commutativity of the sections of `R` enters once, in checking that the annihilator is an
`R`-submodule, and it is taken as a hypothesis `∀ X a b, a * b = b * a` rather than through a
`CommRing` instance on the sections: the sections of `R` carry a `Ring` instance from `RingCat`,
and installing a `CommRing` instance on the same type as a local instance would put two
multiplicative structures in scope throughout the file (R19's failure mode). With the hypothesis,
`a • r • m = r • a • m` is two applications of `smul_smul`.

Left exactness reuses `Stacks.Sheaves.RingedPoint.preservesFiniteLimits_moduleSheafFunctor` and
`.reflectsFiniteLimits_moduleSheafFunctor`, which are stated for an arbitrary site and sheaf of
rings even though they live in the ringed-point chapter; nothing about a point is used in them.

`Stacks.SheafOfModules.restrictₛₗ_id_apply` repeats `PresheafOfModules.restrictₛₗ_id_apply` from
`SheafificationTensor.lean`, deliberately: importing the tensor-sheafification development for a
one-line lemma would be the wrong dependency. The right fix is to move that lemma and its
companion out of `SheafificationTensor.lean` into a basic module, which is
a repo-tier change with existing importers and so is left for a later structure pass. The
companion `restrictₛₗ_comp_apply` is repeated for the same reason — Mathlib's
`PresheafOfModules.map_comp_apply` is about `M.map` rather than `M.restrictₛₗ`, which is the same
function but not the same term, so `rw` cannot use it.

The right adjoint is produced by `CategoryTheory.isLeftAdjoint_iff_hasTerminal_costructuredArrow`
rather than built by hand: the terminal object of `CostructuredArrow i_* G` is the annihilator of
`I` in `G`, pulled back along the isomorphism that the essential-image criterion supplies.

## References

* [Stacks Project, Lemma 18.29.2 (Tag 08M3)](https://stacks.math.columbia.edu/tag/08M3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite

universe w v u v' u'

namespace Stacks.SheafOfModules

section Annihilator

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{w}} (M : SheafOfModules.{w} R)

/-- Restricting a section of a sheaf of modules along the identity leaves it unchanged.

This duplicates `PresheafOfModules.restrictₛₗ_id_apply`, which the library has in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SheafificationTensor.lean`; that module is the
tensor-sheafification development and is the wrong thing to depend on for a one-line lemma. See
the implementation notes. -/
theorem restrictₛₗ_id_apply (X : Cᵒᵖ) (m : M.val.obj X) : M.val.restrictₛₗ (𝟙 X) m = m := by
  show M.val.presheaf.map (𝟙 X) m = m
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- Restriction of sections of a sheaf of modules is functorial. Duplicates
`PresheafOfModules.restrictₛₗ_comp_apply`; see `restrictₛₗ_id_apply`. -/
theorem restrictₛₗ_comp_apply {X Y Z : Cᵒᵖ} (g : X ⟶ Y) (h : Y ⟶ Z) (m : M.val.obj X) :
    M.val.restrictₛₗ (g ≫ h) m = M.val.restrictₛₗ h (M.val.restrictₛₗ g m) :=
  M.val.map_comp_apply g h m

variable (hcomm : ∀ (X : Cᵒᵖ) (a b : R.obj.obj X), a * b = b * a)
  (I : (_root_.SheafOfModules.unit R).Submodule)

include hcomm in
/-- The ideal transporter: sections of `M` all of whose restrictions are annihilated by `I`.

This is a subsheaf of `M` — stability under restriction is immediate from the definition, and the
sheaf condition follows from `M` being separated — and it is the largest subsheaf of `M` that `I`
annihilates. -/
noncomputable def annihilatorSubmodule : M.Submodule where
  obj X :=
    { carrier := {m | ∀ (Y : Cᵒᵖ) (g : X ⟶ Y) (a : R.obj.obj Y),
        a ∈ I.obj Y → a • M.val.restrictₛₗ g m = 0}
      zero_mem' := by
        intro Y g a _
        rw [map_zero, smul_zero]
      add_mem' := by
        intro m n hm hn Y g a ha
        simp only [map_add, smul_add, hm Y g a ha, hn Y g a ha, add_zero]
      smul_mem' := by
        intro r m hm Y g a ha
        rw [map_smulₛₗ, smul_smul, hcomm Y _ _, ← smul_smul, hm Y g a ha, smul_zero] }
  map {X Y} g := by
    intro m hm Z h a ha
    rw [← restrictₛₗ_comp_apply]
    exact hm Z (g ≫ h) a ha
  isSheaf {X} m hm := by
    intro Y g a ha
    apply M.isSheaf.isSeparated _ _ (J.pullback_stable g.unop hm)
    intro Z h hh
    change M.val.restrictₛₗ h.op (a • M.val.restrictₛₗ g m) = M.val.restrictₛₗ h.op 0
    rw [map_smulₛₗ, map_zero, ← restrictₛₗ_comp_apply]
    have hz := hh (op Z) (𝟙 _) (R.obj.map h.op a) (I.map h.op ha)
    change _ • M.val.restrictₛₗ (𝟙 (op Z)) (M.val.restrictₛₗ (g ≫ h.op) m) = 0 at hz
    rwa [restrictₛₗ_id_apply] at hz

/-- Membership in the ideal transporter, unfolded. -/
theorem mem_annihilatorSubmodule_obj (X : Cᵒᵖ) (m : M.val.obj X) :
    m ∈ (annihilatorSubmodule M hcomm I).obj X ↔
      ∀ (Y : Cᵒᵖ) (g : X ⟶ Y) (a : R.obj.obj Y), a ∈ I.obj Y →
        a • M.val.restrictₛₗ g m = 0 :=
  Iff.rfl

/-- `I` annihilates the ideal transporter, section by section. -/
theorem smul_annihilatorSubmodule_eq_zero (X : Cᵒᵖ) (a : R.obj.obj X) (ha : a ∈ I.obj X)
    (m : (annihilatorSubmodule M hcomm I).toSheafOfModules.val.obj X) : a • m = 0 := by
  apply Subtype.ext
  show a • m.val = (0 : M.val.obj X)
  have h := (mem_annihilatorSubmodule_obj M hcomm I X m.val).mp m.property X (𝟙 X) a ha
  rwa [restrictₛₗ_id_apply] at h

variable {N : SheafOfModules.{w} R}

/-- A morphism into `M` from a sheaf of modules annihilated by `I` factors through the ideal
transporter. -/
noncomputable def annihilatorLift
    (hN : ∀ (X : Cᵒᵖ) (a : R.obj.obj X), a ∈ I.obj X → ∀ m : N.val.obj X, a • m = 0)
    (φ : N ⟶ M) : N ⟶ (annihilatorSubmodule M hcomm I).toSheafOfModules where
  val :=
    { app X := ModuleCat.ofHom
        ((φ.val.app X).hom.codRestrict ((annihilatorSubmodule M hcomm I).obj X) (fun m ↦
          (mem_annihilatorSubmodule_obj M hcomm I X _).mpr (fun Y g a ha ↦
            calc a • M.val.restrictₛₗ g ((φ.val.app X) m)
                = a • (φ.val.app Y) (N.val.restrictₛₗ g m) :=
                  congrArg (fun z ↦ a • z)
                    (PresheafOfModules.naturality_apply φ.val g m).symm
              _ = (φ.val.app Y) (a • N.val.restrictₛₗ g m) :=
                  ((φ.val.app Y).hom.map_smul a _).symm
              _ = (φ.val.app Y) 0 := congrArg _ (hN Y a ha _)
              _ = 0 := map_zero _)))
      naturality := by
        intro X Y g
        ext m
        exact Subtype.ext (PresheafOfModules.naturality_apply φ.val g m) }

/-- The factorization of `annihilatorLift` through the inclusion of the ideal transporter is the
original morphism. -/
theorem annihilatorLift_comp_ι
    (hN : ∀ (X : Cᵒᵖ) (a : R.obj.obj X), a ∈ I.obj X → ∀ m : N.val.obj X, a • m = 0)
    (φ : N ⟶ M) :
    annihilatorLift M hcomm I hN φ ≫ (annihilatorSubmodule M hcomm I).ι = φ :=
  rfl

end Annihilator

section LeftAdjoint

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{w}} (hcomm : ∀ (X : Cᵒᵖ) (a b : R.obj.obj X), a * b = b * a)
  (I : (_root_.SheafOfModules.unit R).Submodule)

include hcomm in
/-- **A fully faithful functor whose essential image is the `I`-annihilated modules is a left
adjoint.** Its right adjoint sends a sheaf of `R`-modules `G` to the largest subsheaf of `G`
annihilated by `I`, which lies in the essential image and is therefore the terminal object of the
category of objects of the source over `G`.

This is the step of Stacks 08M3 that makes the direct image right exact: the direct image is fully
faithful and has that essential image. -/
theorem isLeftAdjoint_of_essImage_eq_annihilated {A : Type u'} [Category.{v'} A]
    (F : A ⥤ SheafOfModules.{w} R) (hF : F.FullyFaithful)
    (h : ∀ G, F.essImage G ↔ ∀ (X : Cᵒᵖ) (a : R.obj.obj X),
      a ∈ I.obj X → ∀ m : G.val.obj X, a • m = 0) :
    F.IsLeftAdjoint := by
  classical
  refine isLeftAdjoint_iff_hasTerminal_costructuredArrow.mpr fun M ↦ ?_
  obtain ⟨N, ⟨e⟩⟩ := (h (annihilatorSubmodule M hcomm I).toSheafOfModules).mpr
    (smul_annihilatorSubmodule_eq_zero M hcomm I)
  let t : CostructuredArrow F M :=
    CostructuredArrow.mk (e.hom ≫ (annihilatorSubmodule M hcomm I).ι)
  let lift (c : CostructuredArrow F M) : c ⟶ t :=
    CostructuredArrow.homMk
      (hF.preimage (annihilatorLift M hcomm I ((h _).mp (F.obj_mem_essImage c.left)) c.hom ≫
        e.inv)) (by
          dsimp only [t, CostructuredArrow.mk_right, CostructuredArrow.mk_hom_eq_self]
          rw [hF.map_preimage, Category.assoc, e.inv_hom_id_assoc]
          exact annihilatorLift_comp_ι M hcomm I _ c.hom)
  exact (IsTerminal.ofUniqueHom lift fun c φ ↦ CostructuredArrow.hom_ext _ _ <|
    hF.map_injective <| (cancel_mono (e.hom ≫ (annihilatorSubmodule M hcomm I).ι)).mp <|
      φ.w.trans (lift c).w.symm).hasTerminal

end LeftAdjoint

end Stacks.SheafOfModules

namespace AlgebraicGeometry


/-- The sheaf of rings underlying the structure sheaf of the source of a closed immersion of
ringed topoi. This mirrors `AlgebraicGeometry.ClosedRingedImmersion.targetRingSheaf`, which the
library already has; both take the site implicitly, which is what makes them usable in a
statement. -/
noncomputable abbrev ClosedRingedImmersion.sourceRingSheaf
    (S : ClosedRingedImmersion.{v, u, v', u', w}) : Sheaf S.source.J RingCat.{w} :=
  letI := S.hasSheafComposeForget₂Source
  Stacks.SheafOfModules.Tensor.ringSheaf S.source.O

/-- The sections of the structure sheaf of the target of a closed immersion of ringed topoi
commute. -/
theorem ClosedRingedImmersion.targetRingSheaf_mul_comm
    (S : ClosedRingedImmersion.{v, u, v', u', w}) (U : S.target.Cᵒᵖ)
    (a b : S.targetRingSheaf.obj.obj U) : a * b = b * a :=
  mul_comm (G := ToType (S.target.O.obj.obj U)) a b

/-- **Stacks Project, Tag 08M3.** The direct image of sheaves of modules along a closed immersion
of ringed topoi with locally surjective structure map is exact.

Left exactness: the underlying sheaf of sets of the direct image is the direct image of the
underlying sheaf of sets, the latter preserves finite limits because it is a right adjoint, and
the underlying-sheaf functor on sheaves of modules preserves and reflects them. Right exactness:
the direct image is fully faithful with essential image the modules annihilated by the kernel
ideal, hence a left adjoint, hence preserves all colimits. -/
@[stacks 08M3 "exactness", sga "4 IV 13.6" "special case"]
theorem ClosedRingedImmersion.pushforwardModules_exact
    (S : ClosedRingedImmersion.{v, u, v', u', w}) :
    exactFunctor (_root_.SheafOfModules.{w} S.sourceRingSheaf)
      (_root_.SheafOfModules.{w} S.targetRingSheaf) S.hom.pushforwardModules := by
  classical
  let Usrc : _root_.SheafOfModules.{w} S.sourceRingSheaf ⥤ Sheaf S.source.J (Type w) :=
    Sheaf.moduleSheafFunctor S.sourceRingSheaf
  let Utgt : _root_.SheafOfModules.{w} S.targetRingSheaf ⥤ Sheaf S.target.J (Type w) :=
    Sheaf.moduleSheafFunctor S.targetRingSheaf
  have hUsrc : PreservesFiniteLimits Usrc :=
    Stacks.Sheaves.RingedPoint.preservesFiniteLimits_moduleSheafFunctor.{v, u, w}
      S.source.J S.sourceRingSheaf
  have hUtgt : PreservesFiniteLimits Utgt :=
    Stacks.Sheaves.RingedPoint.preservesFiniteLimits_moduleSheafFunctor.{v', u', w}
      S.target.J S.targetRingSheaf
  have hUtgt' : ReflectsFiniteLimits Utgt :=
    Stacks.Sheaves.RingedPoint.reflectsFiniteLimits_moduleSheafFunctor.{v', u', w}
      S.target.J S.targetRingSheaf
  have hpush : PreservesLimits S.hom.toToposHom.pushforward :=
    S.hom.toToposHom.adj.rightAdjoint_preservesLimits
  have hcomp : PreservesFiniteLimits (Usrc ⋙ S.hom.toToposHom.pushforward) :=
    comp_preservesFiniteLimits _ _
  have hlim : PreservesFiniteLimits (S.hom.pushforwardModules ⋙ Utgt) :=
    preservesFiniteLimits_of_natIso S.hom.pushforwardModulesUnderlyingIso.symm
  have hleft : PreservesFiniteLimits S.hom.pushforwardModules :=
    preservesFiniteLimits_of_reflects_of_preserves _ Utgt
  have hadj : S.hom.pushforwardModules.IsLeftAdjoint :=
    Stacks.SheafOfModules.isLeftAdjoint_of_essImage_eq_annihilated
      S.targetRingSheaf_mul_comm S.ideal _ S.pushforwardModules_fullyFaithful.some
      S.pushforwardModules_essImage_iff_ideal_annihilates
  rw [exactFunctor_iff]
  exact ⟨hleft, inferInstance⟩

end AlgebraicGeometry

end
