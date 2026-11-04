module

public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.PushforwardSupport
public import StacksFrontier.AlgebraicGeometry.Cohomology.ZeroDimensionalSupport.Vanishing
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Kernel
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Vanishing
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonInjectivityClosed
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.DevissageChow
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.DirectImageCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ProperSupportCompactification
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.TwoIdealAdicQuotient
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.Coproduct
public import StacksCore.Tactic.StacksAttribute

/-!
# Pushing a coherent adic system forward along an open immersion

Let `p : X ⟶ S` be separated and locally of finite type, let `U ⊆ X` be open and let `ℐ` be a
quasi-coherent sheaf of ideals on `X`. The direct image along the open immersion `U.ι : U ⟶ X`
does **not** preserve coherence, and *a fortiori* does not carry `Coh(U, ℐ|_U)` into
`Coh(X, ℐ)`. This file shows that it does so on the systems whose support is **proper over the
base**, and builds the resulting functor

  `Coh_{support proper over S}(U, ℐ|_U) ⥤ Coh_{support proper over S}(X, ℐ)`.

That functor is the one construction missing behind the binder `hTransport` of
`Stacks.Algebraization.isProper_systemAnnihilatorIdeal_of_transport`
(`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/ProperSupportAlgebraization.lean`,
whose module docstring records the gap: "What is not in this library is the functor pushing a
coherent adic system on `Y` forward to `Y'` along the open immersion `j`, without which `β` cannot
be produced"). The last two sections produce `β`.

## Why properness of the support, and not any property of the immersion, is what works

A coherent sheaf on `U` whose support is proper over `S` is, set-theoretically, supported on a
closed subset of `U` whose image in `X` is **closed** —
`AlgebraicGeometry.exists_closeds_image_isProperOver`, which consumes separatedness of `p` — and
contained in `U`. The two opens `U` and `X ∖ j(Supp)` then cover `X`; on the first the direct
image is a direct image from the open itself and on the second it vanishes. This is [Stacks, Tag
0CYJ] for coherence, and the same two-element cover discharges the quotient clause of
`Stacks.Coherent.IsCoherentAdicSystem`. Nothing here is a property of the immersion: it is the
same mechanism as in `AlgebraicGeometry.isClosedImmersion_subschemeι_vanishingIdeal_comp`, whose
docstring makes the point that the work is done by properness of the closed set.

No single closed subscheme of `U` can be used instead. A coherent adic system is *not* annihilated
by one quasi-coherent ideal sheaf — that it is annihilated by one cutting out a subscheme proper
over the base is exactly the conclusion of [Stacks, Tag 088E] — so the system cannot be presented
as a direct image along a closed immersion, which is what would have let
`Stacks.Coherent.isCoherentAdicSystem_pushforward_closedImmersion` be applied directly. The
annihilator ideal sheaf of each *term* does cut out the support, but it varies with the term, and
the quotient clause relates two consecutive terms.

## Main definitions

* `Stacks.Algebraization.pushforwardCoherentAdicSystemsProperOver` — **the functor**, termwise
  direct image along `U.ι` on the coherent adic systems with support proper over the base.

## Main results

* `Stacks.Algebraization.isCoherent_pushforward_opens_of_isProperOver` and
  `Stacks.Algebraization.hasProperSupport_pushforward_opens_of_isProperOver` — **the module
  statement**: the direct image along `U.ι` of a coherent module whose support is proper over `S`
  is coherent and again has support proper over `S`.
* `Stacks.Algebraization.supp_subset_supp_obj_zero` — every term of a coherent adic system is
  supported where the first one is, which is what makes the hypothesis of the above available at
  every level from the hypothesis at level `0`. Unconditional.
* `Stacks.Algebraization.idealPowerMultiple_pushforward_eq_bot_of_comap` — annihilation by
  `(ℐ 𝒪_Y) ᵐ` ascends to annihilation of the direct image by `ℐ ᵐ`, along an **arbitrary**
  morphism of schemes.
* `Stacks.Algebraization.isIso_directImageQuotientComparison_of_supp_subset` — **the quotient
  clause**: the comparison `δ` of [Stacks, Tag 088B] along `U.ι` is an isomorphism for a coherent
  module whose support has closed image inside `U`.
* `Stacks.Algebraization.isCoherentAdicSystem_pushforward_opens_of_isProperOver` — **the system
  statement**: the termwise direct image along `U.ι` of a coherent adic system along `ℐ|_U` whose
  first term is supported in a closed subset of `U` proper over `S` is a coherent adic system
  along `ℐ`.
* `Stacks.Algebraization.isProperOver_comp_of_isClosed_image` — a closed subset of `U` whose image
  in `X` is closed is proper over `S` when `X` is; the converse of
  `AlgebraicGeometry.exists_closeds_image_isProperOver` for an open immersion.
* `Stacks.Algebraization.exists_iso_completionFunctor_of_isProjectiveMorphism` — **`β`.** Over a
  Noetherian `I`-adically complete `A` and for `p : Y' ⟶ Spec A` H-projective, every coherent adic
  system on an open `U ⊆ Y'` along `𝓘|_U` whose support is proper over `A` is isomorphic to the
  completion of a coherent `𝒪_U`-module. Unconditional.
* `Stacks.Algebraization.exists_hasProperSupport_iso_completionFunctor_of_isProjectiveMorphism` —
  the same with the proper support of the module that `hTransport` asks for, from two binders:
  the Nakayama step, and the support of a restriction to an open.

## What remains, precisely

`β` itself is unconditional. For `β` in the shape `hTransport` wants, the algebraizing module must
have support proper over `A`, and that is the source's "the support of the algebraization does not
escape `j(Y)`". Of that argument this library already has everything except one commutative-algebra
step:

* `Stacks.Algebraization.supp_subset_of_mem_zeroLocus_imp_mem` — the escape itself, where
  completeness of `A` and the universal closedness of `p` are consumed. Proved.
* `AlgebraicGeometry.mem_support_baseIdealSheaf` — `p y ∈ V(I)` puts `y` in the support of
  `𝓘 = I · 𝒪_{Y'}`. Proved.
* **the Nakayama step** — a point of `Supp G'` lying in the support of `𝓘` is in the support of
  `G'/𝓘 G'`. Not in this library; it is the binder `hNak` of
  `Stacks.Algebraization.exists_hasProperSupport_iso_completionFunctor_of_isProjectiveMorphism`.
  Over an affine chart it is Nakayama's lemma for the finite module `Γ(G', V)` at a prime
  containing `I`.

The second binder of that theorem, `hSuppRestrict`, is the statement that the support of the
restriction of a module to an open `U` is the part of its support inside `U`; it is a statement
about stalks, through `AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`, with no geometry in
it. The half of it that this file needs and proves for a direct image is
`Stacks.Algebraization.supp_pushforward_subset_of_isClosed`.

Not done here: the passage from `β` on the compactification to the binder `hTransport`
itself. That asks for the isomorphism over the Chow modification `π : Y ⟶ X` along
`(I · 𝒪_X).comap π`, while the theorems below speak of the open `U ⊆ Y'` along
`(I · 𝒪_{Y'}).comap U.ι`; the two ideal sheaves are equal — both are `I · 𝒪` of the composite to
`Spec A` — but transporting a completion along an equality of ideal sheaves is the move that
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/DirectImageRestrictOpen.lean`
records as timing the kernel out when done with `eqToHom`, and it needs
`Stacks.Algebraization.idealPowerQuotientCongr` rather than a cast.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf` which agrees
with it only at default transparency, so a goal displaying that pattern character for character is
not type-correct at the transparency a rewrite motive is built at. The annihilation statement is
therefore assembled in term mode out of `CategoryTheory.Category.assoc` and `congrArg`, and the
zero morphism it needs is obtained from
`Stacks.Algebraization.submodule_ι_comp_eq_zero_iff` rather than written as `0`, which cannot find
its `Zero` instance in that position.

`set` is used before `intro` in the two theorems with binders: run afterwards it rewrites the
type of the system variable and leaves the hypotheses about it phrased in an inaccessible copy.

## References

* [Stacks Project, Tag 088E](https://stacks.math.columbia.edu/tag/088E)
* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
* [Stacks Project, Tag 0885](https://stacks.math.columbia.edu/tag/0885)
* [Stacks Project, Tag 0CYJ](https://stacks.math.columbia.edu/tag/0CYJ)
* [Stacks Project, Tag 0CYL](https://stacks.math.columbia.edu/tag/0CYL)
* [Stacks Project, Tag 0CYM](https://stacks.math.columbia.edu/tag/0CYM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

open Stacks.Coherent Stacks.Cohomology.FormalFunctions

/-! ### Vanishing of a direct image away from the support -/

/-- A sheaf of modules whose sections over every open contained in `V` vanish restricts to a zero
object on `V`: the sections of the restriction over an open `W` of `V` are the sections of the
module over `V.ι ''ᵁ W ≤ V`. -/
public theorem isZero_restrictFunctor_of_sections_eq_zero {X : Scheme.{u}} (V : X.Opens)
    (M : X.Modules) (h : ∀ W : X.Opens, W ≤ V → ∀ s : Γ(M, W), s = 0) :
    IsZero ((Scheme.Modules.restrictFunctor V.ι).obj M) := by
  refine Stacks.AlgebraicGeometry.GenericPointCoproduct.isZero_of_subsingleton_sections _
    fun W => ⟨fun s t => ?_⟩
  have hle : V.ι ''ᵁ W ≤ V := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  have hinj : Function.Injective (M.restrictAppIso V.ι W).addCommGroupIsoToAddEquiv :=
    (M.restrictAppIso V.ι W).addCommGroupIsoToAddEquiv.injective
  refine hinj ?_
  rw [h _ hle ((M.restrictAppIso V.ι W).addCommGroupIsoToAddEquiv s),
    h _ hle ((M.restrictAppIso V.ι W).addCommGroupIsoToAddEquiv t)]

/-- **The direct image along the inclusion of an open vanishes off a closed set carrying the
support.** Let `U ⊆ X` be open, let `T ⊆ X` be closed with `U.ι '' Supp N ⊆ T`, and let `V` be an
open of `X` disjoint from `T`. Then `(U.ι)_* N` restricts to a zero object on `V`.

A section of `(U.ι)_* N` over an open missing `T` is a section of `N` over an open of `U` missing
`Supp N`, hence zero
(`Stacks.AlgebraicGeometry.CoherentPushforward.pushforward_section_eq_zero_of_notMem`). -/
@[sga "6 IX 1.1" "partial"]
public theorem isZero_restrictFunctor_pushforward_of_supp_subset {X : Scheme.{u}} (U : X.Opens)
    (T : Set X) (N : (U : Scheme.{u}).Modules)
    (hN : U.ι.base '' _root_.SheafOfModules.supp N ⊆ T) (V : X.Opens)
    (hV : ∀ x ∈ V, x ∉ T) :
    IsZero ((Scheme.Modules.restrictFunctor V.ι).obj
      ((Scheme.Modules.pushforward U.ι).obj N)) :=
  isZero_restrictFunctor_of_sections_eq_zero V _ fun W hW s =>
    Stacks.AlgebraicGeometry.CoherentPushforward.pushforward_section_eq_zero_of_notMem
      U T N hN W s fun x hx => hV x (hW hx)

/-- **The support of the direct image along the inclusion of an open lies in any closed set
carrying the image of the support.** -/
public theorem supp_pushforward_subset_of_isClosed {X : Scheme.{u}} (U : X.Opens) (T : Set X)
    (hT : IsClosed T) (N : (U : Scheme.{u}).Modules)
    (hN : U.ι.base '' _root_.SheafOfModules.supp N ⊆ T) :
    _root_.SheafOfModules.supp ((Scheme.Modules.pushforward U.ι).obj N) ⊆ T := by
  intro x hx
  by_contra hxT
  refine Stacks.Algebraization.supp_subset_compl_of_isZero_restrict
    (⟨Tᶜ, hT.isOpen_compl⟩ : X.Opens) _
    (isZero_restrictFunctor_pushforward_of_supp_subset U T N hN
      (⟨Tᶜ, hT.isOpen_compl⟩ : X.Opens) fun y hy => hy) hx ?_
  exact hxT

/-! ### Coherence of the direct image along an open immersion with proper support -/

/-- A closed subset `W` of an open `U` proper over the base has closed image `W'` in `X`, proper
over the base, contained in `U` and containing the image of every subset of `W`. -/
private theorem exists_closeds_image_subset_of_isProperOver {X S : Scheme.{u}} (U : X.Opens)
    (p : X ⟶ S) [IsSeparated p] [LocallyOfFiniteType p] (W : Closeds (U : Scheme.{u}))
    (hW : IsProperOver (U.ι ≫ p) W) :
    ∃ W' : Closeds X, (W' : Set X) ⊆ (U : Set X) ∧ IsProperOver p W' ∧
      ∀ T : Set (U : Scheme.{u}), T ⊆ W → U.ι.base '' T ⊆ (W' : Set X) := by
  obtain ⟨W', hW'eq, hW'p⟩ := exists_closeds_image_isProperOver U.ι p W hW
  refine ⟨W', ?_, hW'p, fun T hT => ?_⟩ <;> rw [hW'eq]
  · rintro x ⟨y, -, rfl⟩
    exact y.2
  · exact Set.image_mono hT

/-- **The direct image along the inclusion of an open of a coherent module whose support is
proper over the base is coherent.** Let `p : X ⟶ S` be separated and locally of finite type, let
`U ⊆ X` be open and let `N` be a coherent `𝒪_U`-module whose support is contained in a closed
subset `W` of `U` which is proper over `S`. Then `(U.ι)_* N` is coherent.

The direct image along an open immersion does **not** preserve coherence in general; what makes
it do so here is that `W` is proper over the base, so its image in `X` is closed
(`AlgebraicGeometry.exists_closeds_image_isProperOver`, which needs `p` separated) and contained
in `U`. [Stacks, Tag 0CYJ],
`Stacks.AlgebraicGeometry.CoherentPushforward.isCoherent_pushforward_of_supp_subset`, then
applies: the two opens `U` and `X ∖ j(W)` cover `X`, the direct image is coherent on the first
because it is a direct image from the open itself and on the second because it vanishes there. -/
public theorem isCoherent_pushforward_opens_of_isProperOver {X S : Scheme.{u}}
    [IsLocallyNoetherian X] (U : X.Opens) (p : X ⟶ S) [IsSeparated p] [LocallyOfFiniteType p]
    (N : (U : Scheme.{u}).Modules) [N.IsCoherent] (W : Closeds (U : Scheme.{u}))
    (hNW : _root_.SheafOfModules.supp N ⊆ (W : Set (U : Scheme.{u})))
    (hW : IsProperOver (U.ι ≫ p) W) :
    ((Scheme.Modules.pushforward U.ι).obj N).IsCoherent := by
  obtain ⟨W', hW'U, -, himg⟩ := exists_closeds_image_subset_of_isProperOver U p W hW
  exact Stacks.AlgebraicGeometry.CoherentPushforward.isCoherent_pushforward_of_supp_subset
    U (W' : Set X) W'.2 hW'U N (himg _ hNW)

/-- **The direct image along the inclusion of an open of a coherent module whose support is
proper over the base again has support proper over the base.** The closed set carrying the
support is the image of `W`, closed and proper over `S` by
`AlgebraicGeometry.exists_closeds_image_isProperOver`. -/
public theorem hasProperSupport_pushforward_opens_of_isProperOver {X S : Scheme.{u}}
    [IsLocallyNoetherian X] (U : X.Opens) (p : X ⟶ S) [IsSeparated p] [LocallyOfFiniteType p]
    (N : (U : Scheme.{u}).Modules) [N.IsCoherent] (W : Closeds (U : Scheme.{u}))
    (hNW : _root_.SheafOfModules.supp N ⊆ (W : Set (U : Scheme.{u})))
    (hW : IsProperOver (U.ι ≫ p) W) :
    HasProperSupport p ((Scheme.Modules.pushforward U.ι).obj N) := by
  have : ((Scheme.Modules.pushforward U.ι).obj N).IsCoherent :=
    isCoherent_pushforward_opens_of_isProperOver U p N W hNW hW
  have : ((Scheme.Modules.pushforward U.ι).obj N).IsFiniteType :=
    _root_.SheafOfModules.IsCoherent.isFiniteType
      (M := (Scheme.Modules.pushforward U.ι).obj N)
  obtain ⟨W', -, hW'p, himg⟩ := exists_closeds_image_subset_of_isProperOver U p W hW
  exact ⟨⟨_root_.SheafOfModules.supp ((Scheme.Modules.pushforward U.ι).obj N),
    _root_.SheafOfModules.isClosed_supp _⟩, rfl, isProperOver_of_le p
    (supp_pushforward_subset_of_isClosed U (W' : Set X) W'.2 N (himg _ hNW)) hW'p⟩

/-! ### All terms of a coherent adic system have the same support -/

/-- **Every term of a coherent adic system is supported where the first one is.** The restriction
of the system to the complement of the support of its zeroth term is again a coherent adic system
(`Stacks.Coherent.isCoherentAdicSystem_restrict`) whose zeroth term vanishes, hence vanishes in
every degree (`Stacks.Coherent.isZero_of_isZero_obj_zero`); so no later term has a point of its
support there.

With the reverse inclusion — each term being a quotient of the next one — this says that all
terms of a coherent adic system have the same support, which is why asking for proper support at
`op 0`, as `Stacks.Algebraization.HasProperSupport` does, is a condition on the whole system. -/
public theorem supp_subset_supp_obj_zero {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (F : CoherentAdicSystems I) (n : ℕ) :
    _root_.SheafOfModules.supp (F.obj.obj (op n)) ⊆
      _root_.SheafOfModules.supp (F.obj.obj (op 0)) := by
  have : _root_.SheafOfModules.IsCoherent.{u} (F.obj.obj (op 0)) := F.property.isCoherent 0
  have : (F.obj.obj (op 0)).IsFiniteType :=
    _root_.SheafOfModules.IsCoherent.isFiniteType (M := F.obj.obj (op 0))
  set V : X.Opens := ⟨(_root_.SheafOfModules.supp (F.obj.obj (op 0)))ᶜ,
    (_root_.SheafOfModules.isClosed_supp (F.obj.obj (op 0))).isOpen_compl⟩ with hV
  have h0 : IsZero ((Scheme.Modules.restrictFunctor V.ι).obj (F.obj.obj (op 0))) :=
    isZero_restrictFunctor_of_sections_eq_zero V _ fun W hW s =>
      AlgebraicGeometry.eq_zero_of_inter_supp_eq_empty (F.obj.obj (op 0)) W
        (Set.eq_empty_iff_forall_notMem.2 fun x hx => hW hx.1 hx.2) s
  have hzero : IsZero ((Scheme.Modules.restrictFunctor V.ι).obj (F.obj.obj (op n))) :=
    Stacks.Coherent.isZero_of_isZero_obj_zero (isCoherentAdicSystem_restrict I V.ι F) h0 n
  intro x hx
  have hmem := supp_subset_compl_of_isZero_restrict V (F.obj.obj (op n)) hzero hx
  simpa [hV] using hmem

/-! ### Annihilation across the direct image along an arbitrary morphism -/

/-- **A module annihilated by `(ℐ 𝒪_Y) ᵐ` has direct image annihilated by `ℐ ᵐ`**, along an
arbitrary morphism of schemes `f : Y ⟶ X`.

`Stacks.Coherent.idealPowerMultiple_pushforward_comp_eq_zero_of_comap` places `ℐ ᵐ (f_*M)`
inside the kernel of the direct image of the projection `M ⟶ M / (ℐ 𝒪_Y) ᵐ M`; when the
projection's source vanishes that projection is split monic, hence so is its direct image, and
the inclusion of `ℐ ᵐ (f_*M)` is therefore the zero morphism.

Compared with `Stacks.Coherent.idealPowerMultiple_pushforward_eq_bot_iff` this is only the easy
direction, but it holds for every morphism of schemes and not only for a closed immersion: the
preimage of an affine open need not be affine, and the cited lemma is exactly what handles
that. -/
public theorem idealPowerMultiple_pushforward_eq_bot_of_comap {X Y : Scheme.{u}} (f : Y ⟶ X)
    (I : X.IdealSheafData) (m : ℕ) (M : Y.Modules)
    (h : idealPowerMultiple (I.comap f) m M = ⊥) :
    idealPowerMultiple I m ((Scheme.Modules.pushforward f).obj M) = ⊥ := by
  have hcond := (submodule_ι_comp_eq_zero_iff (idealPowerMultiple (I.comap f) m M)
    (𝟙 M)).2 (h.le.trans bot_le)
  have hretract : cokernel.π (C := Y.Modules) (idealPowerMultiple (I.comap f) m M).ι ≫
      cokernel.desc (C := Y.Modules) (idealPowerMultiple (I.comap f) m M).ι (𝟙 M) hcond =
      𝟙 M :=
    cokernel.π_desc (C := Y.Modules) _ _ _
  have hsplit : (Scheme.Modules.pushforward f).map
        (cokernel.π (C := Y.Modules) (idealPowerMultiple (I.comap f) m M).ι) ≫
      (Scheme.Modules.pushforward f).map
        (cokernel.desc (C := Y.Modules) (idealPowerMultiple (I.comap f) m M).ι (𝟙 M) hcond) =
      𝟙 _ :=
    ((Scheme.Modules.pushforward f).map_comp _ _).symm.trans
      ((congrArg (Scheme.Modules.pushforward f).map hretract).trans
        ((Scheme.Modules.pushforward f).map_id M))
  have hzero := Stacks.Coherent.idealPowerMultiple_pushforward_comp_eq_zero_of_comap f I m M
  refine (submodule_ι_eq_zero_iff
    (idealPowerMultiple I m ((Scheme.Modules.pushforward f).obj M))).1 ?_
  refine Eq.trans (Category.comp_id _).symm ?_
  refine Eq.trans (congrArg
    (fun z => (idealPowerMultiple I m ((Scheme.Modules.pushforward f).obj M)).ι ≫ z)
    hsplit.symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫ (Scheme.Modules.pushforward f).map
    (cokernel.desc (C := Y.Modules) (idealPowerMultiple (I.comap f) m M).ι (𝟙 M) hcond))
    hzero) ?_
  exact zero_comp

/-! ### Two formalities about zero objects -/

/-- The target of an epimorphism out of a zero object is a zero object. -/
private theorem isZero_of_epi_of_isZero {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    {A B : C} (f : A ⟶ B) [Epi f] (hA : IsZero A) : IsZero B := by
  rw [IsZero.iff_id_eq_zero]
  refine (cancel_epi f).1 ?_
  rw [Category.comp_id, comp_zero]
  exact hA.eq_zero_of_src f

/-- A morphism between zero objects is an isomorphism. -/
private theorem isIso_of_isZero_of_isZero {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    {A B : C} (hA : IsZero A) (hB : IsZero B) (f : A ⟶ B) : IsIso f :=
  ⟨⟨0, hA.eq_of_src _ _, hB.eq_of_tgt _ _⟩⟩

/-! ### The direct-image quotient comparison along an open immersion -/

/-- **The comparison `δ` of [Stacks, Tag 088B] is an isomorphism along the inclusion of an open,
for a coherent module whose support has closed image inside that open.** Let `U ⊆ X` be open, let
`N` be a coherent `𝒪_U`-module and suppose the image of `Supp N` in `X` is contained in a closed
subset `T ⊆ U`. Then

  `δ : ((U.ι)_* N) / ℐ ⁿ⁺¹ ((U.ι)_* N) ⟶ (U.ι)_* (N / (ℐ|_U) ⁿ⁺¹ N)`

of `Stacks.Coherent.directImageQuotientComparison` is an isomorphism.

This is the quotient clause of `Stacks.Coherent.IsCoherentAdicSystem` for a direct image along an
open immersion, and the one place where the geometry is used. Invertibility is local on `X`
(`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict`) and is checked on the cover
`{U, X ∖ T}`:

* on `X ∖ T` the direct image vanishes, by
  `Stacks.Algebraization.isZero_restrictFunctor_pushforward_of_supp_subset`, and so does the
  quotient — restriction preserves cokernels — so `δ` is a morphism between zero objects;
* on `U` the restriction of a direct image along `U.ι` is the identity, the counit
  `AlgebraicGeometry.Scheme.Modules.restrictFunctorAdjCounitIso` being invertible, and
  restriction commutes with the ideal-power quotient
  (`Stacks.Algebraization.restrictIdealPowerQuotientIso`); the restricted `δ` is therefore
  determined, by the quotient projection being an epimorphism, to be the isomorphism which
  `Stacks.Coherent.exists_idealPowerQuotientIsoOfIso` attaches to the counit.

Without the support hypothesis the statement is false: `δ` for the inclusion of a non-dense open
`U ⊆ X` and `N = 𝒪_U` is in general neither injective nor surjective, `(U.ι)_* 𝒪_U` not even
being coherent. -/
public theorem isIso_directImageQuotientComparison_of_supp_subset {X : Scheme.{u}}
    [IsLocallyNoetherian X] (U : X.Opens) (I : X.IdealSheafData) (n : ℕ)
    (N : (U : Scheme.{u}).Modules) [N.IsCoherent]
    (T : Set X) (hT : IsClosed T) (hTU : T ⊆ (U : Set X))
    (hN : U.ι.base '' _root_.SheafOfModules.supp N ⊆ T) :
    IsIso (C := X.Modules)
      (Stacks.Coherent.directImageQuotientComparison U.ι I (n + 1) N) := by
  classical
  have hNU : IsLocallyNoetherian (U : Scheme.{u}) := inferInstance
  set M : X.Modules := (Scheme.Modules.pushforward U.ι).obj N with hM
  set J : (U : Scheme.{u}).IdealSheafData := I.comap U.ι with hJ
  set Q : (U : Scheme.{u}).Modules := idealPowerQuotient J (n + 1) N with hQ
  have hMcoh : M.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentPushforward.isCoherent_pushforward_of_supp_subset
      U T hT hTU N hN
  have hMqc : M.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent M
  -- the support of the quotient is inside that of `N`
  have hQsupp : U.ι.base '' _root_.SheafOfModules.supp Q ⊆ T :=
    (Set.image_mono (Stacks.AlgebraicGeometry.IrreducibleDevissage.supp_subset_of_epi
      (cokernel.π (C := (U : Scheme.{u}).Modules) (idealPowerMultiple J (n + 1) N).ι)
      (inferInstanceAs (Epi (cokernel.π (C := (U : Scheme.{u}).Modules)
        (idealPowerMultiple J (n + 1) N).ι))))).trans hN
  -- the open cover `{X ∖ T, U}`
  set cov : ULift.{u} Bool → X.Opens := fun b =>
    if b.down then ⟨Tᶜ, hT.isOpen_compl⟩ else U with hcov
  have hsup : (⨆ b, cov b) = ⊤ := by
    rw [iSup_ulift, iSup_bool_eq]
    show (⟨Tᶜ, hT.isOpen_compl⟩ : X.Opens) ⊔ U = ⊤
    ext x
    show (x ∈ (⟨Tᶜ, hT.isOpen_compl⟩ : X.Opens) ∨ x ∈ U) ↔ True
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    by_cases hx : x ∈ T
    · exact Or.inr (hTU hx)
    · exact Or.inl hx
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict _ cov
    (TopologicalSpace.IsOpenCover.mk hsup) ?_
  rintro ⟨b⟩
  cases b with
  | true =>
    -- away from `T` both sides vanish
    set V : X.Opens := ⟨Tᶜ, hT.isOpen_compl⟩ with hV
    have hsrc0 : IsZero ((Scheme.Modules.restrictFunctor V.ι).obj M) :=
      isZero_restrictFunctor_pushforward_of_supp_subset U T N hN V fun y hy => hy
    have hsrc : IsZero ((Scheme.Modules.restrictFunctor V.ι).obj
        (idealPowerQuotient I (n + 1) M)) := by
      refine IsZero.of_iso ?_ (PreservesCokernel.iso (Scheme.Modules.restrictFunctor V.ι)
        (idealPowerMultiple I (n + 1) M).ι)
      exact isZero_of_epi_of_isZero
        (cokernel.π ((Scheme.Modules.restrictFunctor V.ι).map
          (idealPowerMultiple I (n + 1) M).ι)) hsrc0
    have htgt : IsZero ((Scheme.Modules.restrictFunctor V.ι).obj
        ((Scheme.Modules.pushforward U.ι).obj Q)) :=
      isZero_restrictFunctor_pushforward_of_supp_subset U T Q hQsupp V fun y hy => hy
    exact (congrArg (fun W : X.Opens => IsIso ((Scheme.Modules.restrictFunctor W.ι).map
      (Stacks.Coherent.directImageQuotientComparison U.ι I (n + 1) N)))
        (show cov ⟨true⟩ = V from rfl)).mpr (isIso_of_isZero_of_isZero hsrc htgt _)
  | false =>
    -- on `U` the restricted comparison is the isomorphism attached to the counit
    have hcovU : cov ⟨false⟩ = U := rfl
    rw [hcovU]
    set R : X.Modules ⥤ (U : Scheme.{u}).Modules := Scheme.Modules.restrictFunctor U.ι with hR
    have hRMcoh : _root_.SheafOfModules.IsCoherent.{u} (R.obj M) :=
      @isCoherent_restrict_of_isOpenImmersion X (U : Scheme.{u}) U.ι _ _ M hMcoh
    set ε := Scheme.Modules.restrictFunctorAdjCounitIso U.ι with hε
    obtain ⟨a, ha⟩ := Stacks.Coherent.exists_idealPowerQuotientIsoOfIso J hRMcoh
      (inferInstanceAs (_root_.SheafOfModules.IsCoherent.{u} N)) (ε.app N) n
    set κ := restrictIdealPowerQuotientIso U.ι I (n + 1) M with hκ
    -- the normalized form of the restricted comparison
    have hnorm : cokernel.π (C := (U : Scheme.{u}).Modules)
          (idealPowerMultiple J (n + 1) (R.obj M)).ι ≫
        (κ.hom ≫ R.map (Stacks.Coherent.directImageQuotientComparison U.ι I (n + 1) N) ≫
          (ε.app Q).hom) =
        (ε.app N).hom ≫ cokernel.π (C := (U : Scheme.{u}).Modules)
          (idealPowerMultiple J (n + 1) N).ι := by
      have hεnat : R.map ((Scheme.Modules.pushforward U.ι).map
            (cokernel.π (C := (U : Scheme.{u}).Modules)
              (idealPowerMultiple J (n + 1) N).ι)) ≫ (ε.app Q).hom =
          (ε.app N).hom ≫ cokernel.π (C := (U : Scheme.{u}).Modules)
            (idealPowerMultiple J (n + 1) N).ι :=
        ε.hom.naturality (cokernel.π (C := (U : Scheme.{u}).Modules)
          (idealPowerMultiple J (n + 1) N).ι)
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      refine Eq.trans (congrArg (fun z => z ≫
        R.map (Stacks.Coherent.directImageQuotientComparison U.ι I (n + 1) N) ≫
          (ε.app Q).hom)
        (cokernel_π_comp_restrictIdealPowerQuotientIso U.ι I (n + 1) M)) ?_
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      refine Eq.trans (congrArg (fun z => z ≫ (ε.app Q).hom)
        ((R.map_comp _ _).symm.trans (congrArg R.map
          (Stacks.Coherent.directImageQuotientComparison_π U.ι I (n + 1) N)))) ?_
      exact hεnat
    -- the quotient projection is an epimorphism, so the two agree
    have hepi : Epi (C := (U : Scheme.{u}).Modules)
        (cokernel.π (C := (U : Scheme.{u}).Modules)
          (idealPowerMultiple J (n + 1) (R.obj M)).ι) := coequalizer.π_epi
    have hsame : κ.hom ≫ R.map
          (Stacks.Coherent.directImageQuotientComparison U.ι I (n + 1) N) ≫
        (ε.app Q).hom = a.hom :=
      (cancel_epi (C := (U : Scheme.{u}).Modules)
        (cokernel.π (C := (U : Scheme.{u}).Modules)
          (idealPowerMultiple J (n + 1) (R.obj M)).ι)).1 (hnorm.trans ha.symm)
    have hσ : IsIso (C := (U : Scheme.{u}).Modules) (κ.hom ≫ R.map
        (Stacks.Coherent.directImageQuotientComparison U.ι I (n + 1) N) ≫
          (ε.app Q).hom) := by
      rw [hsame]
      infer_instance
    have : IsIso (C := (U : Scheme.{u}).Modules)
        (R.map (Stacks.Coherent.directImageQuotientComparison U.ι I (n + 1) N) ≫
          (ε.app Q).hom) :=
      IsIso.of_isIso_comp_left (f := κ.hom) _
    exact IsIso.of_isIso_comp_right
      (R.map (Stacks.Coherent.directImageQuotientComparison U.ι I (n + 1) N)) (ε.app Q).hom

/-! ### The direct image of a coherent adic system along an open immersion -/

/-- **The termwise direct image along the inclusion of an open of a coherent adic system whose
support is proper over the base is a coherent adic system.** Let `p : X ⟶ S` be separated and
locally of finite type, let `U ⊆ X` be open, let `ℐ` be a quasi-coherent ideal sheaf on `X` and
let `(F_n)` be a coherent adic system on `U` along `ℐ|_U` whose zeroth term is supported in a
closed subset `W` of `U` proper over `S`. Then `((U.ι)_* F_n)` is a coherent adic system on `X`
along `ℐ`.

All three clauses of `Stacks.Coherent.IsCoherentAdicSystem` are discharged by the statements
above:

* coherence of `(U.ι)_* F_n` is
  `Stacks.Algebraization.isCoherent_pushforward_opens_of_isProperOver`, every term being
  supported in `W` by `Stacks.Algebraization.supp_subset_supp_obj_zero`;
* annihilation of `(U.ι)_* F_n` by `ℐ ⁿ⁺¹` is
  `Stacks.Algebraization.idealPowerMultiple_pushforward_eq_bot_of_comap`, which needs no
  hypothesis on the morphism at all;
* the quotient clause is
  `Stacks.Algebraization.isIso_directImageQuotientComparison_of_supp_subset` followed by the
  direct image of the quotient isomorphism downstairs, its compatibility with the quotient
  projection being `Stacks.Coherent.directImageQuotientComparison_π` and functoriality.

This is the open-immersion counterpart of
`Stacks.Coherent.isCoherentAdicSystem_pushforward_closedImmersion`, and unlike it is *not*
unconditional: a direct image along an open immersion need not even be coherent. The hypothesis
doing the work is properness of `W` over the base, through
`AlgebraicGeometry.exists_closeds_image_isProperOver` — exactly as in
`AlgebraicGeometry.isClosedImmersion_subschemeι_vanishingIdeal_comp`, and not through any
property of the immersion. -/
public theorem isCoherentAdicSystem_pushforward_opens_of_isProperOver {X S : Scheme.{u}}
    [IsLocallyNoetherian X] (U : X.Opens) (p : X ⟶ S) [IsSeparated p] [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (F : ℕᵒᵖ ⥤ (U : Scheme.{u}).Modules)
    (hF : Stacks.Coherent.IsCoherentAdicSystem (I.comap U.ι) F)
    (W : Closeds (U : Scheme.{u}))
    (hFW : _root_.SheafOfModules.supp (F.obj (op 0)) ⊆ (W : Set (U : Scheme.{u})))
    (hW : IsProperOver (U.ι ≫ p) W) :
    Stacks.Coherent.IsCoherentAdicSystem I (F ⋙ Scheme.Modules.pushforward U.ι) := by
  have hNU : IsLocallyNoetherian (U : Scheme.{u}) := inferInstance
  -- every term is supported in `W`
  have hsupp : ∀ n : ℕ, _root_.SheafOfModules.supp (F.obj (op n)) ⊆
      (W : Set (U : Scheme.{u})) := fun n =>
    (supp_subset_supp_obj_zero (I.comap U.ι) ⟨F, hF⟩ n).trans hFW
  obtain ⟨W', hW'U, -, himg⟩ := exists_closeds_image_subset_of_isProperOver U p W hW
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_⟩
  · have : _root_.SheafOfModules.IsCoherent.{u} (F.obj (op n)) := hF.isCoherent n
    exact isCoherent_pushforward_opens_of_isProperOver U p (F.obj (op n)) W (hsupp n) hW
  · exact idealPowerMultiple_pushforward_eq_bot_of_comap U.ι I (n + 1) (F.obj (op n))
      (hF.idealPowerMultiple_eq_bot n)
  · have : _root_.SheafOfModules.IsCoherent.{u} (F.obj (op (n + 1))) := hF.isCoherent (n + 1)
    have : IsIso (C := X.Modules)
        (Stacks.Coherent.directImageQuotientComparison U.ι I (n + 1) (F.obj (op (n + 1)))) :=
      isIso_directImageQuotientComparison_of_supp_subset U I n (F.obj (op (n + 1)))
        (W' : Set X) W'.2 hW'U (himg _ (hsupp (n + 1)))
    refine ⟨asIso (Stacks.Coherent.directImageQuotientComparison U.ι I (n + 1)
        (F.obj (op (n + 1)))) ≪≫
      (Scheme.Modules.pushforward U.ι).mapIso (hF.quotientIso n), ?_⟩
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ (Scheme.Modules.pushforward U.ι).map (hF.quotientIso n).hom)
          (Stacks.Coherent.directImageQuotientComparison_π U.ι I (n + 1)
            (F.obj (op (n + 1))))).trans
        (((Scheme.Modules.pushforward U.ι).map_comp _ _).symm.trans
          (congrArg (Scheme.Modules.pushforward U.ι).map
            (hF.cokernel_π_comp_quotientIso n))))

/-- **The direct image along the inclusion of an open, as a functor on coherent adic systems with
proper support.** For `p : X ⟶ S` separated and locally of finite type and `U ⊆ X` open, termwise
direct image along `U.ι` is a functor

  `Coh_{support proper over S}(U, ℐ|_U) ⥤ Coh_{support proper over S}(X, ℐ)`.

This is the functor that the transport of [Stacks, Tag 088E] to a projective compactification
needs and that the library did not have. Its action on morphisms is whiskering with
`AlgebraicGeometry.Scheme.Modules.pushforward`, so it is additive on the nose; membership in the
target category is
`Stacks.Algebraization.isCoherentAdicSystem_pushforward_opens_of_isProperOver` for the system
clause and `Stacks.Algebraization.hasProperSupport_pushforward_opens_of_isProperOver` for the
support clause. -/
@[ega "III 5.2.6"]
public def pushforwardCoherentAdicSystemsProperOver {X S : Scheme.{u}} [IsLocallyNoetherian X]
    (U : X.Opens) (p : X ⟶ S) [IsSeparated p] [LocallyOfFiniteType p] (I : X.IdealSheafData) :
    CoherentAdicSystemsProperOver (U.ι ≫ p) (I.comap U.ι) ⥤
      CoherentAdicSystemsProperOver p I :=
  ObjectProperty.lift
    (fun G : Stacks.Coherent.CoherentAdicSystems I => HasProperSupport p (G.obj.obj (op 0)))
    (ObjectProperty.lift (Stacks.Coherent.IsCoherentAdicSystem I)
      (ObjectProperty.ι (fun G : Stacks.Coherent.CoherentAdicSystems (I.comap U.ι) =>
          HasProperSupport (U.ι ≫ p) (G.obj.obj (op 0))) ⋙
        ObjectProperty.ι (Stacks.Coherent.IsCoherentAdicSystem (I.comap U.ι)) ⋙
          (Functor.whiskeringRight _ _ _).obj (Scheme.Modules.pushforward U.ι))
      (fun G => by
        obtain ⟨Z, hZeq, hZp⟩ := G.property
        exact isCoherentAdicSystem_pushforward_opens_of_isProperOver U p I G.obj.obj
          G.obj.property Z hZeq.ge hZp))
    (fun G => by
      obtain ⟨Z, hZeq, hZp⟩ := G.property
      have : _root_.SheafOfModules.IsCoherent.{u} (G.obj.obj.obj (op 0)) :=
        G.obj.property.isCoherent 0
      exact hasProperSupport_pushforward_opens_of_isProperOver U p
        (G.obj.obj.obj (op 0)) Z hZeq.ge hZp)

/-! ### The comparison `β` on a projective compactification -/

/-- An algebraization `G'` of the direct image along `U.ι` of a system `𝓖` on `U` restricts to an
algebraization of `𝓖`: restricting a direct image along `U.ι` back along `U.ι` is the identity. -/
private def iso_completion_restrictCoherentModules {Y' : Scheme.{u}} [IsLocallyNoetherian Y']
    (U : Y'.Opens) (I : Y'.IdealSheafData) (𝓖 : ℕᵒᵖ ⥤ (U : Scheme.{u}).Modules)
    (h : Stacks.Coherent.IsCoherentAdicSystem I (𝓖 ⋙ Scheme.Modules.pushforward U.ι))
    (G' : AlgebraicGeometry.SheafOfModules.CoherentModules Y'.ringCatSheaf)
    (e : (completionFunctor Y' I).obj G' ≅ ⟨𝓖 ⋙ Scheme.Modules.pushforward U.ι, h⟩) :
    𝓖 ≅ ((completionFunctor (U : Scheme.{u}) (I.comap U.ι)).obj
      (restrictCoherentModules U.ι G')).obj :=
  (Functor.associator 𝓖 (Scheme.Modules.pushforward U.ι) (Scheme.Modules.restrictFunctor U.ι) ≪≫
    Functor.isoWhiskerLeft 𝓖 (Scheme.Modules.restrictFunctorAdjCounitIso U.ι) ≪≫
      𝓖.rightUnitor).symm ≪≫
    (Functor.isoWhiskerRight ((ObjectProperty.ι (Stacks.Coherent.IsCoherentAdicSystem I)).mapIso e)
      (Scheme.Modules.restrictFunctor U.ι)).symm ≪≫ completionRestrictOpenIso U.ι I G'

/-- **The source's isomorphism `β`, on an open of a scheme projective over the base.** Let `A` be
Noetherian and complete with respect to `I`, let `p : Y' ⟶ Spec A` be H-projective and let
`U ⊆ Y'` be open. Then every coherent adic system `𝓖` on `U` along `𝓘|_U`, `𝓘 = I · 𝒪_{Y'}`,
whose first term is supported in a closed subset of `U` proper over `A`, is isomorphic to the
completion of a coherent `𝒪_U`-module.

This is the step of the proof of [Stacks, Tag 088E] which the library was missing, and the
functor of
`Stacks.Algebraization.pushforwardCoherentAdicSystemsProperOver` is what makes it available:

* push `𝓖` forward to `Y'` along `U.ι`, obtaining an object of `Coh(Y', 𝓘)` —
  `Stacks.Algebraization.isCoherentAdicSystem_pushforward_opens_of_isProperOver`;
* algebraize it there by the projective case of Grothendieck existence,
  `Stacks.Algebraization.isEquivalenceCompletionFunctorOfIsProjectiveMorphism_holds`, which holds
  outright: an equivalence is essentially surjective, so the pushforward is the completion of a
  coherent `𝒪_{Y'}`-module `G'`;
* restrict back to `U`. Completion commutes with restriction to an open
  (`Stacks.Algebraization.completionRestrictOpenIso`), and restricting a direct image along `U.ι`
  back along `U.ι` is the identity, the counit
  `AlgebraicGeometry.Scheme.Modules.restrictFunctorAdjCounitIso` being invertible; whiskering the
  two into the algebraization isomorphism gives `β`.

Only the isomorphism is produced here. For `β` in the shape the binder `hTransport` of
`Stacks.Algebraization.isProper_systemAnnihilatorIdeal_of_transport` asks for, the module `G`
must in addition have support proper over `A`, which is the content of
`Stacks.Algebraization.exists_hasProperSupport_iso_completionFunctor_of_isProjectiveMorphism`
below. -/
@[ega "III 5.2.5" "more general", ega "III 5.2.6" "partial"]
public theorem exists_iso_completionFunctor_of_isProjectiveMorphism
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {Y' : Scheme.{u}} (p : Y' ⟶ Spec (.of A))
    (hp : AlgebraicGeometry.IsProjectiveMorphism p) (U : Y'.Opens) :
    letI : IsProper p := isProper_of_isProjectiveMorphism p hp
    letI : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian p
    ∀ (𝓖 : Stacks.Coherent.CoherentAdicSystems ((baseIdealSheaf A I p).comap U.ι))
      (W : Closeds (U : Scheme.{u})),
      _root_.SheafOfModules.supp (𝓖.obj.obj (op 0)) ⊆ (W : Set (U : Scheme.{u})) →
      IsProperOver (U.ι ≫ p) W →
        ∃ G : AlgebraicGeometry.SheafOfModules.CoherentModules (U : Scheme.{u}).ringCatSheaf,
          Nonempty (𝓖.obj ≅ ((completionFunctor (U : Scheme.{u})
            ((baseIdealSheaf A I p).comap U.ι)).obj G).obj) := by
  let : IsProper p := isProper_of_isProjectiveMorphism p hp
  let : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsLocallyNoetherian (U : Scheme.{u}) := inferInstance
  intro 𝓖 W hGW hW
  -- the direct image of the system, an object of `Coh(Y', 𝓘)`
  set 𝓗 : Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I p) :=
    ⟨𝓖.obj ⋙ Scheme.Modules.pushforward U.ι,
      isCoherentAdicSystem_pushforward_opens_of_isProperOver U p (baseIdealSheaf A I p)
        𝓖.obj 𝓖.property W hGW hW⟩ with h𝓗
  -- the projective case of Grothendieck existence algebraizes it
  have hequiv : (completionFunctor Y' (baseIdealSheaf A I p)).IsEquivalence :=
    isEquivalenceCompletionFunctorOfIsProjectiveMorphism_holds A I p hp
  set G' := (completionFunctor Y' (baseIdealSheaf A I p)).objPreimage 𝓗 with hG'
  set e4 := (completionFunctor Y' (baseIdealSheaf A I p)).objObjPreimageIso 𝓗 with he4
  exact ⟨restrictCoherentModules U.ι G', ⟨iso_completion_restrictCoherentModules U
    (baseIdealSheaf A I p) 𝓖.obj 𝓗.property G' e4⟩⟩

/-! ### Properness of a closed subset of an open whose image is closed -/

/-- **A closed subset of an open subscheme whose image is closed in the ambient is proper over the
base, as soon as the ambient is.** Let `p : Y' ⟶ S` be proper, let `U ⊆ Y'` be open and let `C` be
a closed subset of `U` whose image in `Y'` is closed. Then `C` is proper over `S`.

This is the converse of `AlgebraicGeometry.exists_closeds_image_isProperOver` in the case of an
open immersion, and it is where the escape of the support is cashed in: the reduced closed
subscheme on `C` maps to `Y'` by an immersion with closed range, hence by a closed immersion
(`AlgebraicGeometry.IsClosedImmersion.of_isPreimmersion`), and the composite of a closed
immersion with a proper morphism is proper. -/
public theorem isProperOver_comp_of_isClosed_image {Y' S : Scheme.{u}} (U : Y'.Opens)
    (p : Y' ⟶ S) [IsProper p] (C : Closeds (U : Scheme.{u}))
    (hC : IsClosed (U.ι.base '' (C : Set (U : Scheme.{u})))) :
    IsProperOver (U.ι ≫ p) C := by
  have hrange : Set.range ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι ≫ U.ι).base =
      U.ι.base '' (C : Set (U : Scheme.{u})) := by
    have h := Set.range_comp U.ι.base (Scheme.IdealSheafData.vanishingIdeal C).subschemeι.base
    rw [show ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι ≫ U.ι).base.hom =
      U.ι.base.hom ∘ (Scheme.IdealSheafData.vanishingIdeal C).subschemeι.base.hom from rfl]
    rw [h, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have : IsClosedImmersion
      ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι ≫ U.ι) :=
    IsClosedImmersion.of_isPreimmersion _ (hrange ▸ hC)
  show IsProper ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι ≫ U.ι ≫ p)
  rw [← Category.assoc]
  infer_instance

/-! ### `β` with proper support: the shape `hTransport` asks for -/

/-- **The source's isomorphism `β`, with the proper support of `G` that `hTransport` asks for.**
Same data as `Stacks.Algebraization.exists_iso_completionFunctor_of_isProjectiveMorphism`, plus
the two statements about supports which that theorem does not need and which this library does
not carry:

* `hNak` — **the Nakayama step**: a point of the support of a coherent module on `Y'` which lies
  in the support of `𝓘 = I · 𝒪_{Y'}` is in the support of the first term `G'/𝓘 G'` of the
  completion of that module. Over an affine chart this is Nakayama's lemma for the finite module
  `Γ(G', V)` at a prime containing `I`, and it is the only ingredient of the escape of the support
  which is missing: `Stacks.Algebraization.supp_subset_of_mem_zeroLocus_imp_mem` consumes
  completeness of `A` and the universal closedness of `p` and is already proved, and
  `AlgebraicGeometry.mem_support_baseIdealSheaf` converts `p y ∈ V(I)` into membership in the
  support of `𝓘`;
* `hSuppRestrict` — the support of the restriction of a module to an open is the part of its
  support lying in that open, a statement about stalks
  (`AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`) with no geometry in it.

Granted these, the whole of `hTransport`'s conclusion over the compactification is proved: the
escape puts `Supp G'` inside `U`, so the image of `Supp(G'|_U)` is `Supp G'`, closed in `Y'`; `Y'`
is proper over `A` because `p` is H-projective, so that closed set is proper over `A`
(`AlgebraicGeometry.isProperOver_of_isProper`), and
`Stacks.Algebraization.isProperOver_comp_of_isClosed_image` carries the properness back down to
`U`. -/
@[ega "III 5.2.6"]
public theorem exists_hasProperSupport_iso_completionFunctor_of_isProjectiveMorphism
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {Y' : Scheme.{u}} (p : Y' ⟶ Spec (.of A))
    (hp : AlgebraicGeometry.IsProjectiveMorphism p) (U : Y'.Opens) :
    letI : IsProper p := isProper_of_isProjectiveMorphism p hp
    letI : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian p
    (∀ (F : AlgebraicGeometry.SheafOfModules.CoherentModules Y'.ringCatSheaf) (y : Y'),
        y ∈ _root_.SheafOfModules.supp F.obj →
        y ∈ (baseIdealSheaf A I p).support →
          y ∈ _root_.SheafOfModules.supp
            (((completionFunctor Y' (baseIdealSheaf A I p)).obj F).obj.obj (op 0))) →
    (∀ F : Y'.Modules, U.ι.base '' _root_.SheafOfModules.supp
        ((Scheme.Modules.restrictFunctor U.ι).obj F) =
        _root_.SheafOfModules.supp F ∩ (U : Set Y')) →
    ∀ (𝓖 : Stacks.Coherent.CoherentAdicSystems ((baseIdealSheaf A I p).comap U.ι))
      (W : Closeds (U : Scheme.{u})),
      _root_.SheafOfModules.supp (𝓖.obj.obj (op 0)) ⊆ (W : Set (U : Scheme.{u})) →
      IsProperOver (U.ι ≫ p) W →
        ∃ G : AlgebraicGeometry.SheafOfModules.CoherentModules (U : Scheme.{u}).ringCatSheaf,
          HasProperSupport (U.ι ≫ p) G.obj ∧
          Nonempty (𝓖.obj ≅ ((completionFunctor (U : Scheme.{u})
            ((baseIdealSheaf A I p).comap U.ι)).obj G).obj) := by
  let : IsProper p := isProper_of_isProjectiveMorphism p hp
  let : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsLocallyNoetherian (U : Scheme.{u}) := inferInstance
  set R : Y'.Modules ⥤ (U : Scheme.{u}).Modules := Scheme.Modules.restrictFunctor U.ι with hR
  set 𝓘 : Y'.IdealSheafData := baseIdealSheaf A I p with h𝓘
  intro hNak hSuppRestrict 𝓖 W hGW hW
  set 𝓗 : Stacks.Coherent.CoherentAdicSystems 𝓘 :=
    ⟨𝓖.obj ⋙ Scheme.Modules.pushforward U.ι,
      isCoherentAdicSystem_pushforward_opens_of_isProperOver U p 𝓘 𝓖.obj 𝓖.property W hGW hW⟩
    with h𝓗
  have hequiv : (completionFunctor Y' 𝓘).IsEquivalence :=
    isEquivalenceCompletionFunctorOfIsProjectiveMorphism_holds A I p hp
  set G' := (completionFunctor Y' 𝓘).objPreimage 𝓗 with hG'
  set e4 := (completionFunctor Y' 𝓘).objObjPreimageIso 𝓗 with he4
  have hG'coh : _root_.SheafOfModules.IsCoherent.{u} G'.obj := G'.property
  have : G'.obj.IsFiniteType := _root_.SheafOfModules.IsCoherent.isFiniteType (M := G'.obj)
  -- the first term of the completion of `G'` is the direct image of the first term of `𝓖`
  have hfirst : _root_.SheafOfModules.supp
      (((completionFunctor Y' 𝓘).obj G').obj.obj (op 0)) ⊆
      _root_.SheafOfModules.supp
        ((Scheme.Modules.pushforward U.ι).obj (𝓖.obj.obj (op 0))) :=
    Stacks.AlgebraicGeometry.IrreducibleDevissage.supp_subset_of_epi
      (((ObjectProperty.ι (Stacks.Coherent.IsCoherentAdicSystem 𝓘)).mapIso
        e4).app (op 0)).inv inferInstance
  -- the support of that direct image is inside `U`
  obtain ⟨W', hW'U, -, himg⟩ := exists_closeds_image_subset_of_isProperOver U p W hW
  have : _root_.SheafOfModules.IsCoherent.{u} (𝓖.obj.obj (op 0)) := 𝓖.property.isCoherent 0
  have hpushU : _root_.SheafOfModules.supp
      ((Scheme.Modules.pushforward U.ι).obj (𝓖.obj.obj (op 0))) ⊆ (U : Set Y') :=
    (supp_pushforward_subset_of_isClosed U (W' : Set Y') W'.2 (𝓖.obj.obj (op 0))
      (himg _ hGW)).trans hW'U
  -- the escape of the support
  have hescape : _root_.SheafOfModules.supp G'.obj ⊆ (U : Set Y') := by
    refine supp_subset_of_mem_zeroLocus_imp_mem A I p G'.obj U.isOpen fun y hy hyI => ?_
    exact hpushU (hfirst (hNak G' y hy
      (mem_support_baseIdealSheaf I p
        (fun z hz => (PrimeSpectrum.mem_zeroLocus _ _).1 hyI hz))))
  -- the restriction of `G'` to `U`, and its proper support
  set G : AlgebraicGeometry.SheafOfModules.CoherentModules (U : Scheme.{u}).ringCatSheaf :=
    restrictCoherentModules U.ι G' with hG
  have hGcoh : _root_.SheafOfModules.IsCoherent.{u} G.obj := G.property
  have : G.obj.IsFiniteType := _root_.SheafOfModules.IsCoherent.isFiniteType (M := G.obj)
  have himage : U.ι.base '' _root_.SheafOfModules.supp G.obj =
      _root_.SheafOfModules.supp G'.obj := by
    rw [hG, show (restrictCoherentModules U.ι G').obj = R.obj G'.obj from rfl, hR,
      hSuppRestrict G'.obj]
    exact Set.inter_eq_self_of_subset_left hescape
  refine ⟨G, ⟨⟨_root_.SheafOfModules.supp G.obj,
    _root_.SheafOfModules.isClosed_supp G.obj⟩, rfl, ?_⟩, ?_⟩
  · refine isProperOver_comp_of_isClosed_image U p
      ⟨_root_.SheafOfModules.supp G.obj, _root_.SheafOfModules.isClosed_supp G.obj⟩ ?_
    show IsClosed (U.ι.base '' _root_.SheafOfModules.supp G.obj)
    rw [himage]
    exact _root_.SheafOfModules.isClosed_supp G'.obj
  · exact ⟨iso_completion_restrictCoherentModules U 𝓘 𝓖.obj 𝓗.property G' e4⟩

end Stacks.Algebraization

end
