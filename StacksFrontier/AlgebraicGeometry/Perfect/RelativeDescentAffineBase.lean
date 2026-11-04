module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentDerivedHom

/-!
# Tag 0DI7 reduced to the affine case over an affine open of the base

The proof of Stacks 0DI7 runs the induction principle of Stacks 08DR **twice**: first over the
quasi-compact opens `W₀` of `S₀`, to reduce to `S₀` affine, and only then over the quasi-compact
opens of `X₀`, to reduce to `X₀` affine. The affine input of the second induction is therefore
not "`V₀` is an affine open of `X₀`" but "`V₀` is an affine open of `X₀` carried into an affine
open `W₀` of `S₀`" — and that is what the ring-theoretic Tag 0DHX can be read at, because for
such a `V₀` the whole restricted situation becomes a filtered system of *rings*: `g_i^{-1}(W₀)`
is affine, with ring `Rᵢ`, the inclusion `V₀ ⟶ S₀` factors through `W₀ = Spec R₀`, and
`Vᵢ = Sᵢ ×_{S₀} V₀ = g_i^{-1}(W₀) ×_{W₀} V₀` has ring `Rᵢ ⊗_{R₀} Γ(V₀)`, which is exactly the
shape of the system Tag 0DHX consumes.

`AlgebraicGeometry.RelativeDescentSituation.restrictHomDescent_of_isAffineOpen_of_sup` runs only
the second induction, so its hypothesis `haffine` quantifies over *every* affine open of `X₀`,
including those contained in no preimage of an affine open of `S₀`. Over such a `V₀` the stages
`Vᵢ` are still affine, but the system of their rings is not of the form `Rᵢ ⊗_{R₀} A₀`, and the
Tor hypothesis on `L₀` remains a condition over the *sheaf* `π₀^{-1}𝒪_{S₀}` rather than over a
ring; so `haffine` in that form is not what Tag 0DHX read through Tags 08E5, 0DHY and 06Z0
delivers, and discharging it needs the first induction as well. This file supplies the reduction
with the affine hypothesis restricted to the affine opens the Stacks proof actually uses.

What makes it possible is that the induction principle of Stacks 08DR only ever needs its base
case for affine opens drawn from a family that is downward closed and locally full: the
intersections the induction creates inside an affine open `W` of the family are finite unions of
basic opens of `W`, which stay in the family. So the first half of the file is Stacks 08DR
relative to such a family, and the second half applies it to the family of affine opens of `X₀`
contained in the preimage of an affine open of `S₀`.

## Main results

* `Stacks.AlgebraicGeometry.CompactOpenInduction.of_isCompact_of_basis`: **Stacks 08DR relative
  to a family of opens.** If `Q` is a downward-closed family of opens containing `⊥` such that
  every point of `X` has an affine open neighbourhood in `Q`, and `P` holds for the affine opens
  in `Q` and is stable under the Mayer--Vietoris union step with the affine summand in `Q`, then
  `P` holds for every quasi-compact open of the quasi-separated scheme `X`.
* `Stacks.AlgebraicGeometry.CompactOpenInduction.top_of_basis`: its conclusion at `X` itself.
* In `AlgebraicGeometry.RelativeDescentSituation`,
  `restrictHomDescent_of_isAffineOpen_over_affine_of_sup` and
  `homDescent_of_isAffineOpen_over_affine_of_sup`: **the induction of Stacks 08DR for Tag
  0DI7 with the Stacks-correct affine hypothesis**, reducing Tag 0DI7 to Tag 0DI7 for the affine
  opens of `X₀` lying over an affine open of `S₀`, together with the Mayer--Vietoris union step
  for such affine opens.

## Implementation notes

The family-relative induction follows the unrelativised proof in
`StacksFrontier/AlgebraicGeometry/CompactOpenInduction/Basic.lean` step for step, with two changes.
The affine step carries `Q W` along: the basic opens of `W` are affine and below `W`, so they
are in `Q`, and `D(f) ⊓ D(g) = D(fg)` keeps the induction inside the family. The general step
cannot call `AlgebraicGeometry.compact_open_induction_on`, which supplies arbitrary affine opens
from `X.affineOpens`, so the finite union is produced by hand from a cover of the quasi-compact
open by affine opens of `Q`, obtained from the basis of affine opens; the intersection with the
affine summand is then quasi-compact inside an affine open of `Q` and the affine step applies.

The family-relative induction is a statement about an arbitrary scheme and belongs in
`StacksFrontier/AlgebraicGeometry/CompactOpenInduction/`; it is kept here only because that file is
outside the subtree this module was written in.

`Nonempty`-freeness is deliberate: `⊥` is an affine open of every scheme, `Q ⊥` is required
explicitly, and the family of affine opens over an affine open of `S₀` contains `⊥` because `⊥`
is an affine open of `S₀`.

## References

* [Stacks Project, Tag 0DI7](https://stacks.math.columbia.edu/tag/0DI7)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
* [Stacks Project, Tag 0DHX](https://stacks.math.columbia.edu/tag/0DHX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.AlgebraicGeometry.CompactOpenInduction

/-! ### The induction principle of Stacks 08DR relative to a family of opens -/

variable {X : Scheme.{u}} {P Q : X.Opens → Prop}
  (hbot : Q ⊥)
  (hmono : ∀ V W : X.Opens, V ≤ W → Q W → Q V)
  (hcover : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ Q V ∧ x ∈ V)
  (h₁ : ∀ V : X.Opens, IsAffineOpen V → Q V → P V)
  (h₂ : ∀ U V : X.Opens, IsCompact (U : Set X) → IsAffineOpen V → Q V →
    P U → P V → P (U ⊓ V) → P (U ⊔ V))

include hmono hcover in
/-- The affine opens belonging to a downward-closed, locally full family of opens form a basis of
the topology. -/
theorem exists_isAffineOpen_mem_le_of_basis (U : X.Opens) (x : X) (hx : x ∈ U) :
    ∃ V : X.Opens, IsAffineOpen V ∧ Q V ∧ x ∈ V ∧ V ≤ U := by
  obtain ⟨W, hWaff, hWQ, hxW⟩ := hcover x
  obtain ⟨f, hf, hxf⟩ := hWaff.exists_basicOpen_le (V := U) ⟨x, hx⟩ hxW
  exact ⟨X.basicOpen f, hWaff.basicOpen f, hmono _ _ (X.basicOpen_le f) hWQ, hxf, hf⟩

/-- A finite union of compact opens is compact. -/
private theorem isCompact_iSup_finset {ι : Type*} (V : ι → X.Opens)
    (hV : ∀ i, IsCompact (V i : Set X)) (s : Finset ι) :
    IsCompact ((⨆ i ∈ s, V i : X.Opens) : Set X) := by
  simp only [Opens.coe_iSup]
  exact s.finite_toSet.isCompact_biUnion fun i _ => hV i

/-- A compact open with an open `F x ≤ S` around each of its points is a finite union of them. -/
private theorem exists_finset_iSup_eq_of_isCompact {S : X.Opens} (hS : IsCompact (S : Set X))
    (F : S → X.Opens) (hmem : ∀ x, (x : X) ∈ F x) (hle : ∀ x, F x ≤ S) :
    ∃ s : Finset S, S = ⨆ i ∈ s, F i := by
  classical
  obtain ⟨s, hs⟩ := hS.elim_finite_subcover (fun x : S => (F x : Set X))
    (fun x => (F x).isOpen) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hmem ⟨x, hx⟩⟩)
  refine ⟨s, le_antisymm (fun x hx => ?_) (iSup_le fun i => iSup_le fun _ => hle i)⟩
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hs hx)
  exact Opens.mem_iSup.2 ⟨i, Opens.mem_iSup.2 ⟨hi, hxi⟩⟩

/-- Induction on the cardinality of an index set for properties of finite unions of opens,
where the step may also use the property for other families `V d'`. -/
private theorem of_finset_iSup_of_step {δ ι : Type*} [DecidableEq ι] (V : δ → ι → X.Opens)
    (h0 : P ⊥)
    (hstep : ∀ (d : δ) (s : Finset ι) (a : ι), a ∈ s → (∀ d', P (⨆ i ∈ s.erase a, V d' i)) →
      P ((⨆ i ∈ s.erase a, V d i) ⊔ V d a)) :
    ∀ (n : ℕ) (s : Finset ι) (d : δ), s.card ≤ n → P (⨆ i ∈ s, V d i) := by
  intro n
  induction n with
  | zero =>
    intro s d hs
    obtain rfl : s = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hs)
    simpa using h0
  | succ n ih =>
    intro s d hs
    rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · simpa using h0
    · have hcard : (s.erase a).card ≤ n := by
        rw [Finset.card_erase_of_mem ha]
        omega
      have key : (⨆ i ∈ s, V d i) = (⨆ i ∈ s.erase a, V d i) ⊔ V d a := by
        conv_lhs => rw [← Finset.insert_erase ha]
        rw [Finset.iSup_insert, sup_comm]
      rw [key]
      exact hstep d s a ha fun d' => ih _ d' hcard

include hbot hmono h₁ h₂ in
/-- **The affine step of Stacks 08DR, relative to a family of opens.** `P` holds for a finite
union of basic opens of an affine open `W` of the family: those basic opens are again affine
opens of the family, and `D(f) ⊓ D(g) = D(fg)` keeps the induction inside the family. -/
theorem of_iSup_basicOpen_of_basis {W : X.Opens} (hW : IsAffineOpen W) (hWQ : Q W) {ι : Type*} :
    ∀ (n : ℕ) (s : Finset ι) (g : ι → Γ(X, W)), s.card ≤ n →
      P (⨆ i ∈ s, X.basicOpen (g i)) := by
  classical
  intro n s g hs
  refine of_finset_iSup_of_step (fun (g : ι → Γ(X, W)) i => X.basicOpen (g i))
    (h₁ ⊥ (isAffineOpen_bot X) hbot) ?_ n s g hs
  intro g s a _ ih
  refine h₂ _ _ (isCompact_iSup_finset _ (fun i => (hW.basicOpen (g i)).isCompact) _)
    (hW.basicOpen _) (hmono _ _ (X.basicOpen_le _) hWQ) (ih g)
    (h₁ _ (hW.basicOpen _) (hmono _ _ (X.basicOpen_le _) hWQ)) ?_
  have e : (⨆ i ∈ s.erase a, X.basicOpen (g i)) ⊓ X.basicOpen (g a)
      = ⨆ i ∈ s.erase a, X.basicOpen (g i * g a) := by
    simp only [iSup_inf_eq, ← Scheme.basicOpen_mul]
  rw [e]
  exact ih _

include hbot hmono h₁ h₂ in
/-- **The separated case of Stacks 08DR, relative to a family of opens.** `P` holds for every
quasi-compact open contained in an affine open of the family. -/
theorem of_le_isAffineOpen_of_basis {W : X.Opens} (hW : IsAffineOpen W) (hWQ : Q W)
    (S : X.Opens) (hS : IsCompact (S : Set X)) (hSW : S ≤ W) : P S := by
  choose F hF₁ hF₂ using fun x : S => hW.exists_basicOpen_le (V := S) x (hSW x.2)
  obtain ⟨s, hs⟩ := exists_finset_iSup_eq_of_isCompact hS (fun x => X.basicOpen (F x)) hF₂ hF₁
  rw [hs]
  exact of_iSup_basicOpen_of_basis hbot hmono h₁ h₂ hW hWQ s.card s F le_rfl

include hbot hmono h₁ h₂ in
/-- `P` holds for a finite union of affine opens of the family: the intersection of such a union
with one more member is a quasi-compact open of that member, where
`of_le_isAffineOpen_of_basis` applies. -/
theorem of_finset_iSup_of_basis [QuasiSeparatedSpace X] {ι : Type*} (V : ι → X.Opens)
    (hVaff : ∀ i, IsAffineOpen (V i)) (hVQ : ∀ i, Q (V i)) :
    ∀ (n : ℕ) (s : Finset ι), s.card ≤ n → P (⨆ i ∈ s, V i) := by
  classical
  intro n s hs
  refine of_finset_iSup_of_step (fun _ : Unit => V) (h₁ ⊥ (isAffineOpen_bot X) hbot) ?_ n s () hs
  intro _ s a _ ih
  have hUc := isCompact_iSup_finset V (fun i => (hVaff i).isCompact) (s.erase a)
  have hinf : IsCompact (((⨆ i ∈ s.erase a, V i : X.Opens) ⊓ V a : X.Opens) : Set X) := by
    rw [Opens.coe_inf]
    exact QuasiSeparatedSpace.inter_isCompact
      ((⨆ i ∈ s.erase a, V i : X.Opens) : Set X) ((V a : X.Opens) : Set X)
      (⨆ i ∈ s.erase a, V i : X.Opens).isOpen hUc (V a).isOpen (hVaff a).isCompact
  exact h₂ _ _ hUc (hVaff a) (hVQ a) (ih ()) (h₁ _ (hVaff a) (hVQ a))
    (of_le_isAffineOpen_of_basis hbot hmono h₁ h₂ (hVaff a) (hVQ a) _ hinf inf_le_right)

include hbot hmono hcover h₁ h₂ in
/-- **Stacks 08DR relative to a family of opens.** Let `X` be a quasi-separated scheme and `Q` a
downward-closed family of its opens, containing `⊥`, such that every point has an affine open
neighbourhood in `Q`. If `P` holds for the affine opens in `Q`, and `P (U ⊔ V)` holds whenever
`U` is a quasi-compact open, `V` an affine open in `Q` and `P U`, `P V`, `P (U ⊓ V)` hold, then
`P` holds for every quasi-compact open of `X`. -/
theorem of_isCompact_of_basis [QuasiSeparatedSpace X] (S : X.Opens)
    (hS : IsCompact (S : Set X)) : P S := by
  choose F hFaff hFQ hFmem hFle using
    fun x : S => exists_isAffineOpen_mem_le_of_basis hmono hcover S x x.2
  obtain ⟨s, hs⟩ := exists_finset_iSup_eq_of_isCompact hS F hFmem hFle
  rw [hs]
  exact of_finset_iSup_of_basis hbot hmono h₁ h₂ F hFaff hFQ s.card s le_rfl

include hbot hmono hcover h₁ h₂ in
/-- **Stacks 08DR relative to a family of opens, at `X` itself.** -/
theorem top_of_basis [QuasiSeparatedSpace X] [CompactSpace X] : P ⊤ :=
  of_isCompact_of_basis hbot hmono hcover h₁ h₂ ⊤
    (by rw [Opens.coe_top]; exact isCompact_univ)

end Stacks.AlgebraicGeometry.CompactOpenInduction

namespace AlgebraicGeometry.RelativeDescentSituation

variable {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] (D : RelativeDescentSituation.{v, u} I)

attribute [local implicit_reducible] restrict

variable (K₀ L₀ : DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace)))

/-! ### The induction with the affine case taken over an affine open of the base -/

/-- The affine opens of `X₀` contained in the preimage of an affine open of `S₀`. These are the
affine opens over which Tag 0DI7 is the ring-theoretic Tag 0DHX. -/
def IsAffineOpenOverAffine (V₀ : D.X₀.left.Opens) : Prop :=
  ∃ W₀ : (D.descent.system.obj (op D.descent.base)).Opens,
    IsAffineOpen W₀ ∧ V₀ ≤ D.X₀.hom ⁻¹ᵁ W₀

/-- The empty open lies over an affine open of `S₀`, namely over the empty one. -/
theorem isAffineOpenOverAffine_bot : D.IsAffineOpenOverAffine ⊥ :=
  ⟨⊥, isAffineOpen_bot _, bot_le⟩

/-- Lying over an affine open of `S₀` is inherited by smaller opens. -/
theorem isAffineOpenOverAffine_mono {V₀ U₀ : D.X₀.left.Opens} (h : V₀ ≤ U₀)
    (hU₀ : D.IsAffineOpenOverAffine U₀) : D.IsAffineOpenOverAffine V₀ :=
  let ⟨W₀, hW₀, hle⟩ := hU₀
  ⟨W₀, hW₀, h.trans hle⟩

/-- **Every point of `X₀` has an affine open neighbourhood lying over an affine open of `S₀`.**
Choose an affine open of `S₀` around the image of the point, then an affine open of `X₀` around
the point inside its preimage; the affine opens of a scheme are a basis of its topology. -/
theorem exists_isAffineOpen_isAffineOpenOverAffine (x : D.X₀.left) :
    ∃ V₀ : D.X₀.left.Opens, IsAffineOpen V₀ ∧ D.IsAffineOpenOverAffine V₀ ∧ x ∈ V₀ := by
  have base := (Scheme.isBasis_affineOpens
      (D.descent.system.obj (op D.descent.base))).exists_subset_of_mem_open
    (Set.mem_univ (D.X₀.hom.base x)) isOpen_univ
  obtain ⟨-, ⟨W₀, hW₀, rfl⟩, hxW₀, -⟩ := base
  obtain ⟨-, ⟨V₀, hV₀, rfl⟩, hxV₀, hV₀W₀⟩ :=
    (Scheme.isBasis_affineOpens D.X₀.left).exists_subset_of_mem_open
      (show x ∈ (D.X₀.hom ⁻¹ᵁ W₀ : D.X₀.left.Opens) from hxW₀) (D.X₀.hom ⁻¹ᵁ W₀).2
  exact ⟨V₀, hV₀, ⟨W₀, hW₀, hV₀W₀⟩, hxV₀⟩

/-- The induction of Stacks 08DR for an arbitrary property `P` of the quasi-compact opens of `X₀`,
with the affine case taken over an affine open of the base. -/
private theorem induction_of_isAffineOpen_over_affine
    (P : ∀ W : D.X₀.left.Opens, IsCompact (W : Set D.X₀.left) → Prop)
    (haffine : ∀ (V₀ : D.X₀.left.Opens) (hV₀ : IsAffineOpen V₀),
      D.IsAffineOpenOverAffine V₀ → P V₀ hV₀.isCompact)
    (hsup : ∀ (U₀ V₀ : D.X₀.left.Opens) (hU₀ : IsCompact (U₀ : Set D.X₀.left))
      (hV₀ : IsAffineOpen V₀) (_ : D.IsAffineOpenOverAffine V₀)
      (hinf : IsCompact ((U₀ ⊓ V₀ : D.X₀.left.Opens) : Set D.X₀.left))
      (hsupc : IsCompact ((U₀ ⊔ V₀ : D.X₀.left.Opens) : Set D.X₀.left)),
      P U₀ hU₀ → P V₀ hV₀.isCompact → P (U₀ ⊓ V₀) hinf → P (U₀ ⊔ V₀) hsupc)
    (U₀ : D.X₀.left.Opens) (hU₀ : IsCompact (U₀ : Set D.X₀.left)) : P U₀ hU₀ := by
  have : QuasiSeparated D.X₀.hom := D.finitePresentation.quasiSeparated
  have : QuasiSeparatedSpace (D.descent.system.obj (op D.descent.base)) :=
    D.descent.quasiSeparated D.descent.base
  have : QuasiSeparatedSpace D.X₀.left := quasiSeparatedSpace_of_quasiSeparated D.X₀.hom
  refine _root_.Stacks.AlgebraicGeometry.CompactOpenInduction.of_isCompact_of_basis
    (P := fun W => ∀ h : IsCompact (W : Set D.X₀.left), P W h)
    (Q := fun W => D.IsAffineOpenOverAffine W) D.isAffineOpenOverAffine_bot
    (fun _ _ hle hQ => D.isAffineOpenOverAffine_mono hle hQ)
    D.exists_isAffineOpen_isAffineOpenOverAffine (fun W hW hQ _ => haffine W hW hQ) ?_
    U₀ hU₀ hU₀
  intro W V hW hV hVQ hPW hPV hPinf hsupc
  have hinf : IsCompact ((W ⊓ V : D.X₀.left.Opens) : Set D.X₀.left) :=
    QuasiSeparatedSpace.inter_isCompact (W : Set D.X₀.left) (V : Set D.X₀.left) W.isOpen hW
      V.isOpen hV.isCompact
  exact hsup W V hW hV hVQ hinf hsupc (hPW hW) (hPV hV.isCompact) (hPinf hinf)

/-- Tag 0DI7 follows from its restriction to the top open, once `X₀` is compact. -/
private theorem homDescent_of_restrictHomDescent_top_aux (K L : DerivedCategory
    (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace)))
    (h : ∀ hTop : IsCompact ((⊤ : D.X₀.left.Opens) : Set D.X₀.left),
      D.RestrictHomDescent K L ⊤ hTop) : D.HomDescent K L := by
  have : QuasiCompact D.X₀.hom := D.finitePresentation.quasiCompact
  have : CompactSpace (D.descent.system.obj (op D.descent.base)) :=
    D.descent.quasiCompact D.descent.base
  have : CompactSpace D.X₀.left := QuasiCompact.compactSpace_of_compactSpace D.X₀.hom
  have hTop : IsCompact ((⊤ : D.X₀.left.Opens) : Set D.X₀.left) := by
    rw [TopologicalSpace.Opens.coe_top]
    exact isCompact_univ
  exact D.homDescent_of_restrictHomDescent_top K L hTop (h hTop)

/-- **The induction of Stacks 08DR for Tag 0DI7, with the affine case taken over an affine open
of the base.** If Tag 0DI7 holds for the restriction to every affine open of `X₀` lying over an
affine open of `S₀`, and holds for `U₀ ⊔ V₀` whenever it holds for a quasi-compact `U₀`, such a
`V₀` and `U₀ ⊓ V₀`, then it holds for the restriction to every quasi-compact open of `X₀`. -/
theorem restrictHomDescent_of_isAffineOpen_over_affine_of_sup
    (haffine : ∀ (V₀ : D.X₀.left.Opens) (hV₀ : IsAffineOpen V₀),
      D.IsAffineOpenOverAffine V₀ → D.RestrictHomDescent K₀ L₀ V₀ hV₀.isCompact)
    (hsup : ∀ (U₀ V₀ : D.X₀.left.Opens) (hU₀ : IsCompact (U₀ : Set D.X₀.left))
      (hV₀ : IsAffineOpen V₀) (_ : D.IsAffineOpenOverAffine V₀)
      (hinf : IsCompact ((U₀ ⊓ V₀ : D.X₀.left.Opens) : Set D.X₀.left))
      (hsupc : IsCompact ((U₀ ⊔ V₀ : D.X₀.left.Opens) : Set D.X₀.left)),
      D.RestrictHomDescent K₀ L₀ U₀ hU₀ → D.RestrictHomDescent K₀ L₀ V₀ hV₀.isCompact →
        D.RestrictHomDescent K₀ L₀ (U₀ ⊓ V₀) hinf →
          D.RestrictHomDescent K₀ L₀ (U₀ ⊔ V₀) hsupc)
    (U₀ : D.X₀.left.Opens) (hU₀ : IsCompact (U₀ : Set D.X₀.left)) :
    D.RestrictHomDescent K₀ L₀ U₀ hU₀ :=
  D.induction_of_isAffineOpen_over_affine (fun W h => D.RestrictHomDescent K₀ L₀ W h) haffine hsup
    U₀ hU₀

/-- **Tag 0DI7 from the affine case over an affine open of the base and the Mayer--Vietoris union
step.** `X₀` is quasi-compact and quasi-separated over the quasi-compact quasi-separated `S₀`, so
the induction reaches `U₀ = X₀`, where restriction is an isomorphism. -/
theorem homDescent_of_isAffineOpen_over_affine_of_sup
    (haffine : ∀ (V₀ : D.X₀.left.Opens) (hV₀ : IsAffineOpen V₀),
      D.IsAffineOpenOverAffine V₀ → D.RestrictHomDescent K₀ L₀ V₀ hV₀.isCompact)
    (hsup : ∀ (U₀ V₀ : D.X₀.left.Opens) (hU₀ : IsCompact (U₀ : Set D.X₀.left))
      (hV₀ : IsAffineOpen V₀) (_ : D.IsAffineOpenOverAffine V₀)
      (hinf : IsCompact ((U₀ ⊓ V₀ : D.X₀.left.Opens) : Set D.X₀.left))
      (hsupc : IsCompact ((U₀ ⊔ V₀ : D.X₀.left.Opens) : Set D.X₀.left)),
      D.RestrictHomDescent K₀ L₀ U₀ hU₀ → D.RestrictHomDescent K₀ L₀ V₀ hV₀.isCompact →
        D.RestrictHomDescent K₀ L₀ (U₀ ⊓ V₀) hinf →
          D.RestrictHomDescent K₀ L₀ (U₀ ⊔ V₀) hsupc) :
    D.HomDescent K₀ L₀ :=
  D.homDescent_of_restrictHomDescent_top_aux K₀ L₀ fun hTop =>
    D.restrictHomDescent_of_isAffineOpen_over_affine_of_sup K₀ L₀ haffine hsup ⊤ hTop

/-! ### The induction over a family of second arguments -/

section Family

variable (L : ℤ → DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace)))

/-- **The induction of Stacks 08DR for Tag 0DI7 over a family of second arguments.** The
Mayer--Vietoris union step is a five lemma in the long exact sequence of Stacks 08BW, and the five
lemma in degree `n` consumes degrees `n - 1` and `n + 1`; so the inducted property cannot be Tag
0DI7 for a single pair `K₀`, `L₀` and is instead Tag 0DI7 for a whole family `L`, to be taken as
the shifts `L n = L₀⟦n⟧` of the intended second argument. -/
theorem restrictHomDescent_family_of_isAffineOpen_over_affine_of_sup
    (haffine : ∀ (n : ℤ) (V₀ : D.X₀.left.Opens) (hV₀ : IsAffineOpen V₀),
      D.IsAffineOpenOverAffine V₀ → D.RestrictHomDescent K₀ (L n) V₀ hV₀.isCompact)
    (hsup : ∀ (U₀ V₀ : D.X₀.left.Opens) (hU₀ : IsCompact (U₀ : Set D.X₀.left))
      (hV₀ : IsAffineOpen V₀) (_ : D.IsAffineOpenOverAffine V₀)
      (hinf : IsCompact ((U₀ ⊓ V₀ : D.X₀.left.Opens) : Set D.X₀.left))
      (hsupc : IsCompact ((U₀ ⊔ V₀ : D.X₀.left.Opens) : Set D.X₀.left)),
      (∀ n : ℤ, D.RestrictHomDescent K₀ (L n) U₀ hU₀) →
      (∀ n : ℤ, D.RestrictHomDescent K₀ (L n) V₀ hV₀.isCompact) →
      (∀ n : ℤ, D.RestrictHomDescent K₀ (L n) (U₀ ⊓ V₀) hinf) →
        ∀ n : ℤ, D.RestrictHomDescent K₀ (L n) (U₀ ⊔ V₀) hsupc)
    (U₀ : D.X₀.left.Opens) (hU₀ : IsCompact (U₀ : Set D.X₀.left)) (n : ℤ) :
    D.RestrictHomDescent K₀ (L n) U₀ hU₀ :=
  D.induction_of_isAffineOpen_over_affine (fun W h => ∀ m, D.RestrictHomDescent K₀ (L m) W h)
    (fun V hV hQ m => haffine m V hV hQ) hsup U₀ hU₀ n

/-- **Tag 0DI7 over a family of second arguments.** `X₀` is quasi-compact and quasi-separated
over the quasi-compact quasi-separated `S₀`, so the induction reaches `U₀ = X₀`, where
restriction is an isomorphism. -/
theorem homDescent_family_of_isAffineOpen_over_affine_of_sup
    (haffine : ∀ (n : ℤ) (V₀ : D.X₀.left.Opens) (hV₀ : IsAffineOpen V₀),
      D.IsAffineOpenOverAffine V₀ → D.RestrictHomDescent K₀ (L n) V₀ hV₀.isCompact)
    (hsup : ∀ (U₀ V₀ : D.X₀.left.Opens) (hU₀ : IsCompact (U₀ : Set D.X₀.left))
      (hV₀ : IsAffineOpen V₀) (_ : D.IsAffineOpenOverAffine V₀)
      (hinf : IsCompact ((U₀ ⊓ V₀ : D.X₀.left.Opens) : Set D.X₀.left))
      (hsupc : IsCompact ((U₀ ⊔ V₀ : D.X₀.left.Opens) : Set D.X₀.left)),
      (∀ n : ℤ, D.RestrictHomDescent K₀ (L n) U₀ hU₀) →
      (∀ n : ℤ, D.RestrictHomDescent K₀ (L n) V₀ hV₀.isCompact) →
      (∀ n : ℤ, D.RestrictHomDescent K₀ (L n) (U₀ ⊓ V₀) hinf) →
        ∀ n : ℤ, D.RestrictHomDescent K₀ (L n) (U₀ ⊔ V₀) hsupc)
    (n : ℤ) : D.HomDescent K₀ (L n) :=
  D.homDescent_of_restrictHomDescent_top_aux K₀ (L n) fun hTop =>
    D.restrictHomDescent_family_of_isAffineOpen_over_affine_of_sup K₀ L haffine hsup ⊤ hTop n

end Family

end AlgebraicGeometry.RelativeDescentSituation

end
