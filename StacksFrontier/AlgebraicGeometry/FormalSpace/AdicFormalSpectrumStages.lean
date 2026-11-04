module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.ThickeningStage
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.QuasiCoherentDerivedCategory
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleRingsRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOverAdic
import StacksFrontier.AlgebraicGeometry.FormalSpace.SiteQuasiCompact
import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.SmallSite
import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsAndColimits

/-!
# The stages `Spec (A ⧸ I ^ (n + 1))` of the formal spectrum of an adic ring

Let `S` be a scheme, let `A` be an adic topological ring over `S` (Stacks 07E8 (8)) with ideal of
definition `I`, and let `X = Spf A` be its formal spectrum (Stacks 0AIF). Let
`p : 𝒳 → (Sch/S)_{fppf}` be the category fibred in sets attached to the functor `X`
(Stacks 04TM), and let `𝒳_{affine}` be its affine subcategory (Stacks 0H0A), with structure
sheaf `O` (Stacks 0H08). This file contains the geometric input of the proof of Stacks 0H0L:

* the *stages* `Spec (A ⧸ I ^ (n + 1)) → X`, the canonical colimit injections, are objects of
  `𝒳_{affine}`, and they form a functor `ℕ ⥤ 𝒳_{affine}`;
* every object of `𝒳_{affine}` maps to some stage (Formal Spaces, Lemma 0AIA, together with the
  cofinality of the powers of `I` among the weak ideals of definition), and to a given stage in
  at most one way (each stage is a monomorphism into `X`);
* there is a morphism from the `m`-th to the `n`-th stage exactly when `I ^ (n + 1) ≤ I ^ (m + 1)`;
* `O` takes the value `A ⧸ I ^ (n + 1)` on the `n`-th stage, naturally in `n`;
* if the powers of `I` stabilize, `I ^ (N + 1) = I ^ (N + 2)`, then `I ^ (N + 1) = 0` and the
  `N`-th stage is a terminal object of `𝒳_{affine}`; if they never stabilize, the functor
  `ℕ ⥤ 𝒳_{affine}` is fully faithful.

## Main definitions

* `AlgebraicGeometry.FormalSpace.formalSpectrumFibred`,
  `AlgebraicGeometry.FormalSpace.formalSpectrumProjection`: the category fibred in sets `𝒳` of
  Stacks 04TM attached to the formal spectrum, and `p : 𝒳 ⥤ (Sch/S)_{fppf}`.
* `AlgebraicGeometry.FormalSpace.formalSpectrumAffine`: its affine subcategory `𝒳_{affine}`.
* `AlgebraicGeometry.FormalSpace.stage`: the object `Spec (A ⧸ I ^ (n + 1)) → X` of `𝒳_{affine}`.
* `AlgebraicGeometry.FormalSpace.stageHomOfPowLE`, `AlgebraicGeometry.FormalSpace.stageHomOfLE`,
  `AlgebraicGeometry.FormalSpace.stageFunctor`: the morphisms between stages, and the functor
  `ℕ ⥤ 𝒳_{affine}`.
* `AlgebraicGeometry.FormalSpace.stageRingEquiv`: `O(Spec (A ⧸ I ^ (n + 1))) ≃+* A ⧸ I ^ (n + 1)`.
* `AlgebraicGeometry.FormalSpace.IsStage`: the full subcategory `𝒞 ⊆ 𝒳_{affine}` of the stages.
* `AlgebraicGeometry.FormalSpace.isTerminalStage`: the stable case.
* `AlgebraicGeometry.FormalSpace.stageFunctorFullyFaithful`,
  `AlgebraicGeometry.FormalSpace.stageEquivalence`: the strictly decreasing case, in which `𝒞` is
  equivalent to `ℕ`.

## Main results

* `AlgebraicGeometry.FormalSpace.subsingleton_hom_stage` and
  `AlgebraicGeometry.FormalSpace.exists_hom_stage`: every object of `𝒳_{affine}` maps to a stage,
  and to each stage in at most one way.
* `AlgebraicGeometry.FormalSpace.nonempty_hom_stage_iff`: the morphisms between stages.
* `AlgebraicGeometry.FormalSpace.stageRingEquiv_map`: naturality of the ring identification.
* `AlgebraicGeometry.FormalSpace.pow_eq_bot_of_pow_eq_pow_succ`: stable powers of an ideal of
  definition of an adic ring vanish.
* `AlgebraicGeometry.FormalSpace.isCofiltered_structuredArrow`: for every object `U` of
  `𝒳_{affine}` the category of arrows from `U` to a stage is cofiltered, which is the hypothesis
  under which restriction to the stages is an equivalence on quasi-coherent objects (Differential
  Graded Sheaves, Lemma 0GZE).

## Implementation notes

The category fibred in sets of Stacks 04TM, whose morphisms `(U, x) → (V, y)` are the
`f : U → V` with `F(f)(y) = x`, is the *opposite* of Mathlib's category of elements of the
presheaf `X`, because Mathlib's `CategoryTheory.Functor.Elements` of a presheaf on `C` has its
morphisms in the direction of `Cᵒᵖ`. So `formalSpectrumFibred D` is
`(formalSpectrum D).obj.Elementsᵒᵖ` and the projection is the `leftOp` of Mathlib's projection.

The `n`-th stage is indexed by `I ^ (n + 1)` rather than `I ^ n`, so that it exists for every
`n : ℕ` (the ideal `I ^ 0 = A` is open but is a weak ideal of definition only when `A = 0`).
That `I ^ (n + 1)` is a weak ideal of definition, that the topology of `A` is `I`-adic, and that
every weak ideal of definition contains a power of `I`, are proved here from the two hypotheses
the source states (the ring is adic and `I` is an ideal of definition), as is the linearity of
the topology which the thickening property of the stages needs. The source's Noetherian
hypothesis is not used for anything in this file.

The point of `X` over the `n`-th stage is the image of the tautological section of the
sheafified representable under the colimit injection, so that morphisms into a stage are
computed by Yoneda's lemma for sheaves (`CategoryTheory.Sheaf.sectionEquiv`): a morphism
`U → stage n` of `𝒳_{affine}` is a morphism `g` of the site with `h_g ≫ ι_n` equal to the
point of `U`. Each colimit injection `ι_n` is a monomorphism because the transition maps are
closed immersions, which gives uniqueness, and the existence is the factorization of a point of
a filtered colimit of sheaves over a quasi-compact object of the site through a stage
(`AlgebraicGeometry.FormalSpace.compact_map_factors_through_filtered_colimit`, the argument of
Stacks 0AIA), followed by the cofinality of the powers of `I`.

`IsStage` is the property `∃ n, x = stage D hA hI n` of an object `x` of `𝒳_{affine}`.

## References

* [Stacks Project, Tag 0H0L](https://stacks.math.columbia.edu/tag/0H0L)
* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
* [Stacks Project, Tag 04TM](https://stacks.math.columbia.edu/tag/04TM)
* [Stacks Project, Tag 07E8](https://stacks.math.columbia.edu/tag/07E8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Topology

namespace AlgebraicGeometry.FormalSpace

universe u

-- The `ReflQuiver` instance on a category gives a second `Quiver` instance path, which the
-- declarations of `StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum` do not use; with it
-- the hom types of sheaves elaborated here would not match theirs syntactically.
attribute [-instance] CategoryTheory.catToReflQuiver

/-! ### Powers of an ideal of definition of an adic ring -/

section Ideals

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- Once two consecutive powers of an ideal agree, the smaller exponent's power lies in every
higher power. -/
private theorem le_pow_add_of_pow_eq_pow_succ {N : ℕ} (h : I ^ (N + 1) = I ^ (N + 2)) :
    ∀ k : ℕ, I ^ (N + 1) ≤ I ^ (N + 1 + k)
  | 0 => le_rfl
  | k + 1 => by
    calc I ^ (N + 1) = I ^ (N + 1) * I := by rw [← pow_succ, ← h]
      _ ≤ I ^ (N + 1 + k) * I := Ideal.mul_mono_left (le_pow_add_of_pow_eq_pow_succ h k)
      _ = I ^ (N + 1 + (k + 1)) := by rw [← pow_succ, Nat.add_assoc]

/-- If the powers of `I` never stabilize, a containment `I ^ (n + 1) ≤ I ^ (m + 1)` forces
`m ≤ n`. -/
theorem le_of_pow_succ_le_pow_succ (hstrict : ∀ n : ℕ, I ^ (n + 1) ≠ I ^ (n + 2)) {m n : ℕ}
    (h : I ^ (n + 1) ≤ I ^ (m + 1)) : m ≤ n := by
  by_contra hmn
  refine hstrict n (le_antisymm ?_ (Ideal.pow_le_pow_right (by omega)))
  exact h.trans (Ideal.pow_le_pow_right (by omega))

variable [TopologicalSpace A] [IsTopologicalRing A]

/-- A positive power of an ideal of definition of an adic topological ring is a weak ideal of
definition: the topology is adic for every ideal of definition, so the power is open, and its
elements are topologically nilpotent. -/
theorem isWeakIdealOfDefinition_pow_succ_of_isAdic (hA : TopologicalRing.IsAdic A)
    (hI : TopologicalRing.IsIdealOfDefinition I) (n : ℕ) :
    TopologicalRing.IsWeakIdealOfDefinition (I ^ (n + 1)) :=
  TopologicalRing.CompletionOver.isWeakIdealOfDefinition_pow hI
    (TopologicalRing.isAdic_of_isIdealOfDefinition_of_isPreAdic hA.1 hI) n.succ_ne_zero

/-- **Stable powers of an ideal of definition vanish.** If `I` is an ideal of definition of an
adic topological ring and `I ^ (N + 1) = I ^ (N + 2)`, then `I ^ (N + 1) = 0`: the power lies
in every power of `I`, hence in every neighbourhood of zero, and the ring is Hausdorff. -/
theorem pow_eq_bot_of_pow_eq_pow_succ (hA : TopologicalRing.IsAdic A)
    (hI : TopologicalRing.IsIdealOfDefinition I) {N : ℕ} (h : I ^ (N + 1) = I ^ (N + 2)) :
    I ^ (N + 1) = ⊥ := by
  have : T2Space A := hA.2.1
  refine (Submodule.eq_bot_iff _).2 fun x hx ↦ ?_
  by_contra hx0
  obtain ⟨n, hn⟩ := hI.2 ({x}ᶜ : Set A) (isOpen_compl_singleton.mem_nhds (Ne.symm hx0))
  have hxn : x ∈ I ^ n :=
    Ideal.pow_le_pow_right (Nat.le_add_left n (N + 1)) (le_pow_add_of_pow_eq_pow_succ h n hx)
  exact hn hxn rfl

end Ideals

/-! ### The category fibred in sets of the formal spectrum -/

section Fibred

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] [TopologicalSpace A]

/-- **Stacks 04TM for `Spf A`.** The category fibred in sets `𝒳` attached to the formal spectrum:
objects are pairs `(U, x)` with `x ∈ X(U)`, and a morphism `(U, x) ⟶ (V, y)` is a morphism
`f : U ⟶ V` of the site with `X(f)(y) = x`. It is the opposite of Mathlib's category of elements
of the presheaf underlying `Spf A`. -/
abbrev formalSpectrumFibred (D : QuotientSystem B S hS A) : Type (u + 1) :=
  (formalSpectrum D).obj.Elementsᵒᵖ

/-- The projection `p : 𝒳 ⥤ (Sch/S)_{fppf}`, `(U, x) ↦ U`. -/
abbrev formalSpectrumProjection (D : QuotientSystem B S hS A) :
    formalSpectrumFibred D ⥤ BigFppfOver B S hS :=
  (CategoryOfElements.π (formalSpectrum D).obj).leftOp

/-- The affine subcategory `𝒳_{affine}` of the category fibred in sets of the formal spectrum
(Stacks 0H0A): the pairs `(U, x)` with `U` affine. -/
abbrev formalSpectrumAffine (D : QuotientSystem B S hS A) : Type (u + 1) :=
  Stack.AffineCategory B S hS (formalSpectrumProjection D)

/-- The structure sheaf `O` of `𝒳_{affine}` (Stacks 0H08): `O(U, x) = Γ(U, 𝒪_U)`. -/
abbrev formalSpectrumAffineStructure (D : QuotientSystem B S hS A) :
    (formalSpectrumAffine D)ᵒᵖ ⥤ RingCat.{u} :=
  Stack.affineStructurePresheaf B S hS (formalSpectrumProjection D)

end Fibred

/-! ### The stages -/

section Stages

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] {I : Ideal A}
  (D : QuotientSystem B S hS A)
  (hA : TopologicalRing.IsAdic A) (hI : TopologicalRing.IsIdealOfDefinition I)

/-- The weak ideal of definition `I ^ (n + 1)`, as an index of the diagram of quotient spectra
whose colimit is the formal spectrum. -/
def stageIndex (n : ℕ) :
    OrderDual { J : Ideal A // TopologicalRing.IsWeakIdealOfDefinition J } :=
  OrderDual.toDual ⟨I ^ (n + 1), isWeakIdealOfDefinition_pow_succ_of_isAdic hA hI n⟩

/-- The affine scheme `Spec (A ⧸ I ^ (n + 1))` over `S`, as an object of the big fppf site. -/
abbrev stageSiteObject (n : ℕ) : BigFppfOver B S hS :=
  (BigAffineFppf.inclusion B S hS).obj (D.diagram.obj (stageIndex hA hI n))

/-- The canonical colimit injection `Spec (A ⧸ I ^ (n + 1)) → Spf A`. -/
abbrev stageInclusion (n : ℕ) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (stageSiteObject D hA hI n) ⟶
      formalSpectrum D :=
  formalSpectrumInclusion D (stageIndex hA hI n)

/-- The point of `Spf A` over `Spec (A ⧸ I ^ (n + 1))`: the image under the canonical colimit
injection of the tautological section of the sheafified representable. -/
def stagePoint (n : ℕ) : (formalSpectrum D).obj.obj (op (stageSiteObject D hA hI n)) :=
  (stageInclusion D hA hI n).hom.app _
    (Sheaf.tautologicalSection (BigFppfOver.topology B S hS) (stageSiteObject D hA hI n))

/-- Under Yoneda's lemma for sheaves, the colimit injection of a stage is its point. -/
theorem sectionEquiv_stageInclusion (n : ℕ) :
    Sheaf.sectionEquiv (BigFppfOver.topology B S hS) (stageInclusion D hA hI n) =
      stagePoint D hA hI n := by
  rw [stagePoint, Sheaf.tautologicalSection, ← Sheaf.sectionEquiv_comp, Category.id_comp]

/-- **The `n`-th stage** `Spec (A ⧸ I ^ (n + 1)) → Spf A`, as an object of `𝒳_{affine}`. -/
def stage (n : ℕ) : formalSpectrumAffine D :=
  ⟨op ((formalSpectrum D).obj.elementsMk (op (stageSiteObject D hA hI n)) (stagePoint D hA hI n)),
    (D.diagram.obj (stageIndex hA hI n)).property⟩

/-- The object of the site underlying the `n`-th stage is `Spec (A ⧸ I ^ (n + 1))`. -/
@[simp]
theorem formalSpectrumProjection_obj_stage (n : ℕ) :
    (formalSpectrumProjection D).obj (stage D hA hI n).obj = stageSiteObject D hA hI n :=
  rfl

variable {D hA hI}

/-- A morphism of the site from the object under `U` to the `n`-th stage object, pulling the
point of the stage back to the point of `U`, is a morphism `U ⟶ stage n` of `𝒳_{affine}`. -/
def homStageMk {U : formalSpectrumAffine D} {n : ℕ}
    (g : (formalSpectrumProjection D).obj U.obj ⟶ stageSiteObject D hA hI n)
    (hg : (formalSpectrum D).obj.map g.op (stagePoint D hA hI n) = U.obj.unop.2) :
    U ⟶ stage D hA hI n :=
  ObjectProperty.homMk (Quiver.Hom.op ⟨g.op, hg⟩)

/-- The morphism of the site underlying `homStageMk g hg` is `g`. -/
@[simp]
theorem formalSpectrumProjection_map_homStageMk {U : formalSpectrumAffine D} {n : ℕ}
    (g : (formalSpectrumProjection D).obj U.obj ⟶ stageSiteObject D hA hI n)
    (hg : (formalSpectrum D).obj.map g.op (stagePoint D hA hI n) = U.obj.unop.2) :
    (formalSpectrumProjection D).map (homStageMk g hg).hom = g :=
  rfl

/-- Restricting the point of a stage along a morphism of the site is, under Yoneda's lemma for
sheaves, precomposing the colimit injection. -/
theorem map_stagePoint {V : BigFppfOver B S hS} {n : ℕ} (g : V ⟶ stageSiteObject D hA hI n) :
    (formalSpectrum D).obj.map g.op (stagePoint D hA hI n) =
      Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map g ≫
          stageInclusion D hA hI n) := by
  rw [Sheaf.sectionEquiv_map_comp, sectionEquiv_stageInclusion]

/-- A morphism `U ⟶ stage n` of `𝒳_{affine}` makes the triangle over `Spf A` commute: the
colimit injection precomposed with the underlying morphism of the site is the point of `U`. -/
theorem sheafifiedYoneda_map_comp_stageInclusion {U : formalSpectrumAffine D} {n : ℕ}
    (f : U ⟶ stage D hA hI n) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((formalSpectrumProjection D).map f.hom) ≫ stageInclusion D hA hI n =
      (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm U.obj.unop.2 := by
  rw [Equiv.eq_symm_apply]
  exact (map_stagePoint _).symm.trans f.hom.unop.2

variable (D hA hI)

/-- The morphism `Spec (A ⧸ I ^ (m + 1)) → Spec (A ⧸ I ^ (n + 1))` of the site induced by the
quotient map, for `I ^ (n + 1) ≤ I ^ (m + 1)`. -/
def stageSiteObjectHom {m n : ℕ} (h : I ^ (n + 1) ≤ I ^ (m + 1)) :
    stageSiteObject D hA hI m ⟶ stageSiteObject D hA hI n :=
  (BigAffineFppf.inclusion B S hS).map
    (D.diagram.map (homOfLE (show stageIndex hA hI m ≤ stageIndex hA hI n from h)))

/-- On schemes, the morphism between stage objects is `Spec` of the quotient map. -/
theorem toScheme_map_stageSiteObjectHom {m n : ℕ} (h : I ^ (n + 1) ≤ I ^ (m + 1)) :
    (BigFppfOver.toScheme B S hS).map (stageSiteObjectHom D hA hI h) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) :=
  rfl

/-- The colimit injections are compatible with the morphisms between stage objects. -/
@[reassoc]
theorem sheafifiedYoneda_map_stageSiteObjectHom_comp {m n : ℕ} (h : I ^ (n + 1) ≤ I ^ (m + 1)) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (stageSiteObjectHom D hA hI h) ≫
      stageInclusion D hA hI n = stageInclusion D hA hI m :=
  colimit.w (formalSpectrumDiagram D)
    (homOfLE (show stageIndex hA hI m ≤ stageIndex hA hI n from h))

/-- The morphism `stage m ⟶ stage n` of `𝒳_{affine}` given by `Spec` of the quotient map
`A ⧸ I ^ (n + 1) → A ⧸ I ^ (m + 1)`, for `I ^ (n + 1) ≤ I ^ (m + 1)`. -/
def stageHomOfPowLE {m n : ℕ} (h : I ^ (n + 1) ≤ I ^ (m + 1)) :
    stage D hA hI m ⟶ stage D hA hI n :=
  homStageMk (stageSiteObjectHom D hA hI h)
    ((map_stagePoint (stageSiteObjectHom D hA hI h)).trans
      ((congrArg (Sheaf.sectionEquiv (BigFppfOver.topology B S hS))
        (sheafifiedYoneda_map_stageSiteObjectHom_comp D hA hI h)).trans
          (sectionEquiv_stageInclusion D hA hI m)))

/-- The morphism of the site underlying `stageHomOfPowLE` is `stageSiteObjectHom`. -/
@[simp]
theorem formalSpectrumProjection_map_stageHomOfPowLE {m n : ℕ} (h : I ^ (n + 1) ≤ I ^ (m + 1)) :
    (formalSpectrumProjection D).map (stageHomOfPowLE D hA hI h).hom =
      stageSiteObjectHom D hA hI h :=
  rfl

/-- The morphism `stage m ⟶ stage n` for `m ≤ n`: `Spec` of the quotient map
`A ⧸ I ^ (n + 1) → A ⧸ I ^ (m + 1)`. -/
def stageHomOfLE {m n : ℕ} (h : m ≤ n) : stage D hA hI m ⟶ stage D hA hI n :=
  stageHomOfPowLE D hA hI (Ideal.pow_le_pow_right (Nat.succ_le_succ h))

/-! ### Morphisms into a stage -/

/-- The transition maps of the diagram of quotient spectra are monomorphisms: they are closed
immersions. -/
private theorem mono_formalSpectrumDiagram_map [IsLinearTopology A A]
    {i j : OrderDual { J : Ideal A // TopologicalRing.IsWeakIdealOfDefinition J }} (f : i ⟶ j) :
    Mono ((formalSpectrumDiagram D).map f) := by
  have : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map
      ((BigAffineFppf.inclusion B S hS).map (D.diagram.map f))) :=
    (D.isThickening_map_diagram f).1
  exact Sheaf.mono_sheafifiedYoneda_map_of_mono_underlying _ (BigFppfOver.toScheme B S hS)
    ((BigAffineFppf.inclusion B S hS).map (D.diagram.map f)) inferInstance

/-- The colimit injection of a stage is a monomorphism: the transition maps of the diagram of
quotient spectra are closed immersions, hence monomorphisms of represented sheaves, and the
diagram is filtered. -/
instance mono_stageInclusion (n : ℕ) : Mono (stageInclusion D hA hI n) := by
  have : IsLinearTopology A A := by
    obtain ⟨J, -, hJ⟩ := hA.1
    exact hJ ▸ Ideal.isLinearTopology J
  have : IsDirected (OrderDual { J : Ideal A // TopologicalRing.IsWeakIdealOfDefinition J })
      (· ≤ ·) :=
    ⟨fun i j ↦ ⟨OrderDual.toDual ⟨i.1 ⊓ j.1,
      TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right i.2 j.2.1⟩,
      (inf_le_left : i.1 ⊓ j.1 ≤ i.1), (inf_le_right : i.1 ⊓ j.1 ≤ j.1)⟩⟩
  have : Nonempty (OrderDual { J : Ideal A // TopologicalRing.IsWeakIdealOfDefinition J }) :=
    ⟨stageIndex hA hI n⟩
  refine Sheaf.mono_colimit_ι_of_mono_transition (formalSpectrumDiagram D) (fun i j f ↦ ?_) _
  have hclosed : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map
      ((BigAffineFppf.inclusion B S hS).map (D.diagram.map f))) :=
    (D.isThickening_map_diagram f).1
  exact Sheaf.mono_sheafifiedYoneda_map_of_mono_underlying _ (BigFppfOver.toScheme B S hS)
    ((BigAffineFppf.inclusion B S hS).map (D.diagram.map f)) inferInstance

/-- **Morphisms into a stage are unique.** A morphism of `𝒳_{affine}` into a stage is a
morphism over `Spf A`, and the stage maps to `Spf A` by a monomorphism. -/
instance subsingleton_hom_stage (U : formalSpectrumAffine D) (n : ℕ) :
    Subsingleton (U ⟶ stage D hA hI n) := by
  have := bigFppfOver_subcanonical B S hS
  refine ⟨fun f f' ↦ ?_⟩
  have h : (formalSpectrumProjection D).map f.hom = (formalSpectrumProjection D).map f'.hom := by
    apply (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_injective
    exact (cancel_mono (stageInclusion D hA hI n)).1
      ((sheafifiedYoneda_map_comp_stageInclusion f).trans
        (sheafifiedYoneda_map_comp_stageInclusion f').symm)
  exact ObjectProperty.hom_ext _ (Quiver.Hom.unop_inj
    (CategoryOfElements.ext _ _ _ (Quiver.Hom.unop_inj h)))

/-- **Every object of `𝒳_{affine}` maps to a stage** (Stacks 0AIA in the proof of Stacks 0H0L).
A point of `Spf A` over an affine scheme, a quasi-compact object of the site, factors through
one of the quotient spectra `Spec (A ⧸ J)`, `J` a weak ideal of definition; and `J` contains a
power of the ideal of definition `I`. -/
theorem exists_hom_stage (U : formalSpectrumAffine D) : ∃ n, Nonempty (U ⟶ stage D hA hI n) := by
  have := bigFppfOver_subcanonical B S hS
  have : IsDirected (OrderDual { J : Ideal A // TopologicalRing.IsWeakIdealOfDefinition J })
      (· ≤ ·) :=
    ⟨fun i j ↦ ⟨OrderDual.toDual ⟨i.1 ⊓ j.1,
      TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right i.2 j.2.1⟩,
      (inf_le_left : i.1 ⊓ j.1 ≤ i.1), (inf_le_right : i.1 ⊓ j.1 ≤ j.1)⟩⟩
  have : Nonempty (OrderDual { J : Ideal A // TopologicalRing.IsWeakIdealOfDefinition J }) :=
    ⟨stageIndex hA hI 0⟩
  have : IsLinearTopology A A := by
    obtain ⟨J, -, hJ⟩ := hA.1
    exact hJ ▸ Ideal.isLinearTopology J
  let V₀ : BigFppfOver B S hS := (formalSpectrumProjection D).obj U.obj
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj V₀) := U.property
  have hqc := isQuasiCompactObject_over_of_compact_scheme B S hS V₀
  obtain ⟨j, g, hg⟩ := compact_map_factors_through_filtered_colimit (formalSpectrumDiagram D)
    (fun _ _ f ↦ mono_formalSpectrumDiagram_map D f) V₀ hqc
    ((Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm U.obj.unop.2)
  obtain ⟨m, hm0, hm⟩ :=
    TopologicalRing.CompletionOver.exists_pow_le_of_isWeakIdealOfDefinition hI
      (OrderDual.ofDual j).2
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  let t : j ⟶ stageIndex hA hI n := homOfLE (show j ≤ stageIndex hA hI n from hm)
  obtain ⟨g', hg'⟩ : ∃ g' : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V₀ ⟶
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (stageSiteObject D hA hI n),
      g' ≫ stageInclusion D hA hI n =
        (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm U.obj.unop.2 :=
    ⟨g ≫ (formalSpectrumDiagram D).map t, (Category.assoc _ _ _).trans
      ((congrArg (g ≫ ·) (colimit.w (formalSpectrumDiagram D) t)).trans hg)⟩
  refine ⟨n, ⟨homStageMk ((Sheaf.fullyFaithfulSheafifiedYoneda
    (BigFppfOver.topology B S hS)).preimage g') ((map_stagePoint _).trans ?_)⟩⟩
  rw [Functor.FullyFaithful.map_preimage, hg', Equiv.apply_symm_apply]

/-- **The morphisms between stages.** There is a morphism from the `m`-th to the `n`-th stage
exactly when `I ^ (n + 1) ≤ I ^ (m + 1)`. -/
theorem nonempty_hom_stage_iff {m n : ℕ} :
    Nonempty (stage D hA hI m ⟶ stage D hA hI n) ↔ I ^ (n + 1) ≤ I ^ (m + 1) := by
  refine ⟨fun ⟨f⟩ ↦ ?_, fun h ↦ ⟨stageHomOfPowLE D hA hI h⟩⟩
  have := bigFppfOver_subcanonical B S hS
  have hm : I ^ (max m n + 1) ≤ I ^ (m + 1) := Ideal.pow_le_pow_right (by omega)
  have hn : I ^ (max m n + 1) ≤ I ^ (n + 1) := Ideal.pow_le_pow_right (by omega)
  obtain ⟨a, ha⟩ : ∃ a : stageSiteObject D hA hI m ⟶ stageSiteObject D hA hI n,
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map a ≫ stageInclusion D hA hI n =
        stageInclusion D hA hI m :=
    ⟨(formalSpectrumProjection D).map f.hom, (sheafifiedYoneda_map_comp_stageInclusion f).trans
      ((Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm_apply_eq.2
        (sectionEquiv_stageInclusion D hA hI m).symm)⟩
  have h1 : a ≫ stageSiteObjectHom D hA hI hn = stageSiteObjectHom D hA hI hm := by
    apply (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_injective
    refine (cancel_mono (stageInclusion D hA hI (max m n))).1 ?_
    rw [Functor.map_comp, Category.assoc, sheafifiedYoneda_map_stageSiteObjectHom_comp,
      sheafifiedYoneda_map_stageSiteObjectHom_comp, ha]
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (R := CommRingCat.of (A ⧸ I ^ (n + 1)))
    (S := CommRingCat.of (A ⧸ I ^ (m + 1))) ((BigFppfOver.toScheme B S hS).map a)
  have h2 : CommRingCat.ofHom (Ideal.Quotient.factor hn) ≫ ψ =
      CommRingCat.ofHom (Ideal.Quotient.factor hm) := by
    apply Spec.map_injective
    have h4 := congrArg (BigFppfOver.toScheme B S hS).map h1
    rw [Functor.map_comp, toScheme_map_stageSiteObjectHom, toScheme_map_stageSiteObjectHom] at h4
    rw [Spec.map_comp, hψ]
    exact h4
  intro x hx
  have h3 := congrArg (fun φ ↦ φ.hom (Ideal.Quotient.mk (I ^ (max m n + 1)) x)) h2
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero] at h3
  exact Ideal.Quotient.eq_zero_iff_mem.mp h3.symm

/-! ### The functor `ℕ ⥤ 𝒳_{affine}` -/

/-- The stages as a functor `ℕ ⥤ 𝒳_{affine}`, `n ↦ Spec (A ⧸ I ^ (n + 1))`. -/
@[simps obj]
def stageFunctor : ℕ ⥤ formalSpectrumAffine D where
  obj n := stage D hA hI n
  map f := stageHomOfLE D hA hI (leOfHom f)
  map_id _ := (subsingleton_hom_stage D hA hI _ _).elim _ _
  map_comp _ _ := (subsingleton_hom_stage D hA hI _ _).elim _ _

/-- The functor `ℕ ⥤ 𝒳_{affine}` of stages is faithful. -/
instance : (stageFunctor D hA hI).Faithful where
  map_injective _ := Subsingleton.elim _ _

/-- **If the powers of `I` never stabilize, the stages form a full subcategory isomorphic to
`ℕ`:** the functor `ℕ ⥤ 𝒳_{affine}` is fully faithful. -/
def stageFunctorFullyFaithful (hstrict : ∀ n : ℕ, I ^ (n + 1) ≠ I ^ (n + 2)) :
    (stageFunctor D hA hI).FullyFaithful where
  preimage f :=
    homOfLE (le_of_pow_succ_le_pow_succ hstrict ((nonempty_hom_stage_iff D hA hI).1 ⟨f⟩))
  map_preimage _ := (subsingleton_hom_stage D hA hI _ _).elim _ _
  preimage_map _ := Subsingleton.elim _ _

/-- The functor `ℕ ⥤ 𝒳_{affine}` is full when the powers of `I` never stabilize. -/
theorem stageFunctor_full (hstrict : ∀ n : ℕ, I ^ (n + 1) ≠ I ^ (n + 2)) :
    (stageFunctor D hA hI).Full :=
  (stageFunctorFullyFaithful D hA hI hstrict).full

/-! ### The structure sheaf on the stages -/

/-- **The structure sheaf on a stage**: `O(Spec (A ⧸ I ^ (n + 1))) ≃+* A ⧸ I ^ (n + 1)`, the ring
of global functions on an affine scheme. -/
def stageRingEquiv (n : ℕ) :
    (formalSpectrumAffineStructure D).obj (op (stage D hA hI n)) ≃+* A ⧸ I ^ (n + 1) :=
  (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I ^ (n + 1)))).commRingCatIsoToRingEquiv

/-- The identification of the structure sheaf on the stages is natural: restriction along a
morphism between stages is the quotient map. -/
theorem stageRingEquiv_map_stageHomOfPowLE {m n : ℕ} (h : I ^ (n + 1) ≤ I ^ (m + 1))
    (x : (formalSpectrumAffineStructure D).obj (op (stage D hA hI n))) :
    stageRingEquiv D hA hI m
        ((formalSpectrumAffineStructure D).map (stageHomOfPowLE D hA hI h).op x) =
      Ideal.Quotient.factor h (stageRingEquiv D hA hI n x) :=
  ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.factor h))) x

/-- The identification of the structure sheaf on the stages is natural in `n`. -/
theorem stageRingEquiv_map {m n : ℕ} (h : m ≤ n)
    (x : (formalSpectrumAffineStructure D).obj (op (stage D hA hI n))) :
    stageRingEquiv D hA hI m ((formalSpectrumAffineStructure D).map (stageHomOfLE D hA hI h).op x) =
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ h))
        (stageRingEquiv D hA hI n x) :=
  stageRingEquiv_map_stageHomOfPowLE D hA hI _ x

/-! ### The stable case -/

/-- Every object of `𝒳_{affine}` maps to the `N`-th stage once `I ^ (N + 1) = I ^ (N + 2)`. -/
theorem nonempty_hom_stage_of_pow_eq_pow_succ {N : ℕ} (hN : I ^ (N + 1) = I ^ (N + 2))
    (U : formalSpectrumAffine D) : Nonempty (U ⟶ stage D hA hI N) := by
  obtain ⟨k, ⟨f⟩⟩ := exists_hom_stage D hA hI U
  have h : I ^ (N + 1) ≤ I ^ (k + 1) := by
    rw [pow_eq_bot_of_pow_eq_pow_succ hA hI hN]
    exact bot_le
  exact ⟨f ≫ stageHomOfPowLE D hA hI h⟩

/-- **The stable case.** If `I ^ (N + 1) = I ^ (N + 2)`, the `N`-th stage is a terminal object of
`𝒳_{affine}`: every object maps to it, uniquely. -/
def isTerminalStage {N : ℕ} (hN : I ^ (N + 1) = I ^ (N + 2)) :
    IsTerminal (stage D hA hI N) :=
  IsTerminal.ofUniqueHom (fun U ↦ (nonempty_hom_stage_of_pow_eq_pow_succ D hA hI hN U).some)
    fun _ _ ↦ Subsingleton.elim _ _

/-! ### The full subcategory of stages -/

/-- The objects of `𝒳_{affine}` that are stages: the full subcategory `𝒞` of the proof of
Stacks 0H0L. -/
def IsStage : ObjectProperty (formalSpectrumAffine D) :=
  fun x ↦ ∃ n, x = stage D hA hI n

/-- Every `stage n` is a stage. -/
theorem isStage_stage (n : ℕ) : IsStage D hA hI (stage D hA hI n) :=
  ⟨n, rfl⟩

/-- **For every object `U` of `𝒳_{affine}`, the arrows from `U` to a stage form a cofiltered
category.** It is nonempty because `U` maps to some stage, any two arrows are dominated by the one
to the smaller stage, and parallel arrows agree because morphisms into a stage are unique. -/
instance isCofiltered_structuredArrow (U : formalSpectrumAffine D) :
    IsCofiltered (StructuredArrow U (IsStage D hA hI).ι) := by
  have hsub : ∀ X Y : StructuredArrow U (IsStage D hA hI).ι, Subsingleton (X ⟶ Y) := by
    rintro X ⟨Yl, ⟨_, n, rfl⟩, Yh⟩
    exact ⟨fun f g ↦ StructuredArrow.hom_ext _ _
      (ObjectProperty.hom_ext _ ((subsingleton_hom_stage D hA hI _ n).elim _ _))⟩
  have hle : ∀ (X Y : StructuredArrow U (IsStage D hA hI).ι) (a b : ℕ),
      X.right.obj = stage D hA hI a → Y.right.obj = stage D hA hI b → a ≤ b →
        Nonempty (X ⟶ Y) := by
    rintro ⟨Xl, ⟨_, a', ha'⟩, Xh⟩ ⟨Yl, ⟨_, b', hb'⟩, Yh⟩ a b ha hb hab
    dsimp only at ha hb
    subst ha hb
    exact ⟨StructuredArrow.homMk (ObjectProperty.homMk (stageHomOfLE D hA hI hab))
      ((subsingleton_hom_stage D hA hI U b).elim _ _)⟩
  obtain ⟨n, ⟨f⟩⟩ := exists_hom_stage D hA hI U
  have : Nonempty (StructuredArrow U (IsStage D hA hI).ι) :=
    ⟨StructuredArrow.mk (Y := (⟨stage D hA hI n, n, rfl⟩ : (IsStage D hA hI).FullSubcategory))
      f⟩
  refine { cone_objs := fun X Y ↦ ?_, cone_maps := fun X Y f g ↦ ?_ }
  · obtain ⟨a, ha⟩ := X.right.property
    obtain ⟨b, hb⟩ := Y.right.property
    rcases le_total a b with hab | hba
    · exact ⟨X, 𝟙 X, (hle X Y a b ha hb hab).some, trivial⟩
    · exact ⟨Y, (hle Y X b a hb ha hba).some, 𝟙 Y, trivial⟩
  · exact ⟨X, 𝟙 X, (hsub X Y).elim _ _⟩

/-- The stages as a functor into the full subcategory `𝒞` of stages. -/
def stageFunctorToIsStage : ℕ ⥤ (IsStage D hA hI).FullSubcategory :=
  ObjectProperty.lift _ (stageFunctor D hA hI) (isStage_stage D hA hI)

/-- Every object of the full subcategory of stages is isomorphic to some `stage n`. -/
instance : (stageFunctorToIsStage D hA hI).EssSurj where
  mem_essImage Y := by
    obtain ⟨n, hn⟩ := Y.property
    exact ⟨n, ⟨(IsStage D hA hI).fullyFaithfulι.preimageIso (eqToIso hn.symm)⟩⟩

/-- The functor from `ℕ` to the full subcategory of stages is faithful. -/
instance : (stageFunctorToIsStage D hA hI).Faithful where
  map_injective _ := Subsingleton.elim _ _

/-- **If the powers of `I` never stabilize, the full subcategory `𝒞` of stages is equivalent to
`ℕ`**, by `n ↦ Spec (A ⧸ I ^ (n + 1))`. -/
def stageEquivalence (hstrict : ∀ n : ℕ, I ^ (n + 1) ≠ I ^ (n + 2)) :
    ℕ ≌ (IsStage D hA hI).FullSubcategory :=
  have : (stageFunctorToIsStage D hA hI).Full :=
    ⟨fun {m n} f ↦ ⟨homOfLE (le_of_pow_succ_le_pow_succ hstrict
      ((nonempty_hom_stage_iff D hA hI).1 ⟨f.hom⟩)),
      ObjectProperty.hom_ext _ ((subsingleton_hom_stage D hA hI _ _).elim _ _)⟩⟩
  have : (stageFunctorToIsStage D hA hI).IsEquivalence := { }
  (stageFunctorToIsStage D hA hI).asEquivalence

/-- The equivalence `stageEquivalence` sends `n` to the `n`-th stage. -/
@[simp]
theorem stageEquivalence_functor_obj_obj (hstrict : ∀ n : ℕ, I ^ (n + 1) ≠ I ^ (n + 2))
    (n : ℕ) : ((stageEquivalence D hA hI hstrict).functor.obj n).obj = stage D hA hI n :=
  rfl

end Stages

end AlgebraicGeometry.FormalSpace

end
