module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt

/-!
# Stacks 007C — the presheaf of `C^∞` functions on `ℝ^n` and its stalks

Stacks 007C takes `X = ℝ^n` with the Euclidean topology and the presheaf `C^∞_{ℝ^n}` whose
sections over an open `U` are the `C^∞` functions `U → ℝ`, and observes that an element of the
stalk at a point `x` is the same thing as a *germ of a `C^∞` function at `x`*: a `C^∞` function
defined on some open neighbourhood of `x`, two such being identified when they agree near `x`.

The presheaf is `smoothPresheaf`, whose sections over `U` are `SmoothSections`, the quotient of
`SmoothFun` by pointwise equality on `U`. Germs are `SmoothGerm n x`, the subtype of
`Filter.Germ (𝓝 x) ℝ` cut out by `IsSmoothGerm`, for which `isSmoothGerm_iff` gives a
reformulation in terms of the interior of the domain of a representative. The identification of
the stalk with germs is `stalkEquivSmoothGerm`, built from the cocone `smoothGermCocone` over the
diagram of sections on open neighbourhoods of `x`: `stalkToSmoothGerm` is the induced map out of
the colimit and `smoothGermToStalk` its inverse. Finally `smoothGerm_eq_iff` records that two
smooth representatives give the same germ exactly when they are eventually equal along `𝓝 x`.

The sheaf condition for `C^∞_{ℝ^n}`, and its `ℝ`-vector space structure, are not treated here.
-/

@[expose] public section


open Topology Filter TopologicalSpace CategoryTheory Opposite
open CategoryTheory.Limits

/-- Euclidean space `ℝ^n` (as a metric / topological space). -/
abbrev RealN (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A smooth function on an open `U ⊆ ℝ^n`: a real-valued function on the
ambient space together with a proof of `C^∞` smoothness on `U`. -/
structure SmoothFun (n : ℕ) (U : Set (RealN n)) where
  /-- The underlying real-valued function on `ℝ^n`. -/
  toFun : RealN n → ℝ
  /-- The function `toFun` is `C^∞` on `U`. -/
  smooth : ContDiffOn ℝ ⊤ toFun U

/-- Two `SmoothFun n U` are equivalent if they agree pointwise on `U`. -/
def SmoothFun.eqOnU (n : ℕ) (U : Set (RealN n)) (f g : SmoothFun n U) : Prop :=
  Set.EqOn f.toFun g.toFun U

/-- Sections of the presheaf of smooth functions over `U`:
the quotient of `SmoothFun n U` by pointwise equality on `U`. -/
def SmoothSections (n : ℕ) (U : Set (RealN n)) : Type :=
  Quot (SmoothFun.eqOnU n U)

/-- Restriction of smooth sections along an inclusion `V ⊆ U`. -/
def SmoothSections.restrict (n : ℕ) {U V : Set (RealN n)} (h : V ⊆ U) :
    SmoothSections n U → SmoothSections n V :=
  Quot.lift (fun f => Quot.mk _ ⟨f.toFun, f.smooth.mono h⟩)
    (fun f g (hfg : Set.EqOn f.toFun g.toFun U) => Quot.sound fun _x hx => hfg (h hx))

/-- The presheaf on `ℝ^n` whose sections over an open `U` are smooth real-valued
functions on `U`, modulo pointwise equality.  This is the presheaf
`C^∞_{ℝ^n}` from the Stacks tag. -/
noncomputable def smoothPresheaf (n : ℕ) :
    TopCat.Presheaf (Type) (TopCat.of (RealN n)) where
  obj U := SmoothSections n (U.unop : Set (RealN n))
  map {U V} i := ↾(SmoothSections.restrict n (fun _x hx => i.unop.le hx))
  map_id := by
    intro U
    ext s
    induction s using Quot.ind
    rfl
  map_comp := by
    intro U V W f g
    ext s
    induction s using Quot.ind
    rfl

/-- The restriction maps of `smoothPresheaf` restrict representatives. -/
lemma smoothPresheaf_map_mk (n : ℕ) {U V : (Opens (RealN n))ᵒᵖ} (i : U ⟶ V)
    (f : SmoothFun n (U.unop : Set (RealN n))) :
    (smoothPresheaf n).map i (Quot.mk _ f)
      = Quot.mk (SmoothFun.eqOnU n (V.unop : Set (RealN n)))
          ⟨f.toFun, f.smooth.mono i.unop.le⟩ := rfl

/-- A germ `g : Filter.Germ (𝓝 x) ℝ` is *smooth at `x`* if it is represented by
a `C^∞` function on some open neighbourhood of `x`. This is the Stacks notion of
a "germ of a `C^∞`-function at `x`". -/
def IsSmoothGerm (n : ℕ) (x : RealN n) (g : Filter.Germ (𝓝 x) ℝ) : Prop :=
  ∃ U : Set (RealN n), IsOpen U ∧ x ∈ U ∧ ∃ f : RealN n → ℝ,
    ContDiffOn ℝ ⊤ f U ∧ g = (f : Filter.Germ (𝓝 x) ℝ)

/-- The type of smooth germs at `x`. -/
def SmoothGerm (n : ℕ) (x : RealN n) : Type :=
  { g : Filter.Germ (𝓝 x) ℝ // IsSmoothGerm n x g }

/-- The canonical map sending a smooth section over an open neighbourhood `U`
of `x` to the corresponding smooth germ at `x`. -/
noncomputable def sectionToSmoothGerm (n : ℕ) (x : RealN n)
    (U : Set (RealN n)) (hU : IsOpen U) (hxU : x ∈ U)
    (s : SmoothSections n U) : SmoothGerm n x :=
  Quot.liftOn s
    (fun f : SmoothFun n U =>
      (⟨(f.toFun : Filter.Germ (𝓝 x) ℝ),
        ⟨U, hU, hxU, f.toFun, f.smooth, rfl⟩⟩ : SmoothGerm n x))
    (fun f g (hfg : Set.EqOn f.toFun g.toFun U) => Subtype.ext
      (Filter.Germ.coe_eq.mpr (Filter.eventuallyEq_of_mem (hU.mem_nhds hxU) hfg)))

/-- The section-to-germ map is compatible with restriction along open inclusions. -/
lemma sectionToSmoothGerm_restrict (n : ℕ) (x : RealN n)
    {U V : Set (RealN n)} (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    (hxV : x ∈ V) (s : SmoothSections n U) :
    sectionToSmoothGerm n x V hV hxV (SmoothSections.restrict n hVU s)
      = sectionToSmoothGerm n x U hU (hVU hxV) s := by
  induction s using Quot.ind with
  | _ f => rfl

/-- Every smooth germ at `x` arises as the image of some section over some open
neighbourhood of `x` under `sectionToSmoothGerm`. -/
lemma exists_smoothGermWitness (n : ℕ) (x : RealN n) (g : SmoothGerm n x) :
    ∃ (U : Set (RealN n)) (hU : IsOpen U) (hxU : x ∈ U) (s : SmoothSections n U),
      sectionToSmoothGerm n x U hU hxU s = g := by
  obtain ⟨U, hU, hxU, f, hf, hg⟩ := g.prop
  exact ⟨U, hU, hxU, Quot.mk _ ⟨f, hf⟩, Subtype.ext hg.symm⟩

/-- The cocone over the diagram of smooth sections on open neighbourhoods of
`x`, with cocone point `SmoothGerm n x`.  The colimit of this diagram is the
stalk of `smoothPresheaf n` at `x`. -/
noncomputable def smoothGermCocone (n : ℕ) (x : RealN n) :
    Cocone ((TopologicalSpace.OpenNhds.inclusion (X := TopCat.of (RealN n)) x).op ⋙
      smoothPresheaf n) where
  pt := SmoothGerm n x
  ι :=
    { app := fun U =>
        ↾(sectionToSmoothGerm n x (U.unop.1 : Set (RealN n))
            U.unop.1.is_open' U.unop.2)
      naturality := by
        intro U V f
        ext s
        exact sectionToSmoothGerm_restrict n x U.unop.1.is_open' V.unop.1.is_open'
          ((OpenNhds.inclusion (X := TopCat.of (RealN n)) x).map f.unop).le V.unop.2 s }

/-- The forward map (as a categorical morphism in `Type`) from the stalk of the
smooth presheaf at `x` to the type of smooth germs at `x`. -/
noncomputable def stalkToSmoothGermHom (n : ℕ) (x : RealN n) :
    (smoothPresheaf n).stalk (X := TopCat.of (RealN n)) x ⟶ SmoothGerm n x :=
  colimit.desc _ (smoothGermCocone n x)

/-- The forward map as a plain function. -/
noncomputable def stalkToSmoothGerm (n : ℕ) (x : RealN n) :
    (smoothPresheaf n).stalk (X := TopCat.of (RealN n)) x → SmoothGerm n x :=
  stalkToSmoothGermHom n x

/-- The backward map from smooth germs to the stalk of the smooth presheaf at
`x`.  For a smooth germ `g`, we choose a witnessing section `s` over an open
neighbourhood `U ∋ x` and return its germ in the stalk. -/
noncomputable def smoothGermToStalk (n : ℕ) (x : RealN n) (g : SmoothGerm n x) :
    (smoothPresheaf n).stalk (X := TopCat.of (RealN n)) x :=
  let h := exists_smoothGermWitness n x g
  (smoothPresheaf n).germ (X := TopCat.of (RealN n))
    ⟨h.choose, h.choose_spec.choose⟩ x h.choose_spec.choose_spec.choose
    h.choose_spec.choose_spec.choose_spec.choose

/-- The forward map agrees with `sectionToSmoothGerm` after going through the
canonical `germ` map.  This is `colimit.ι_desc_apply` applied to our cocone. -/
lemma stalkToSmoothGerm_germ_apply (n : ℕ) (x : RealN n)
    (U : Set (RealN n)) (hU : IsOpen U) (hxU : x ∈ U) (s : SmoothSections n U) :
    stalkToSmoothGerm n x
        ((smoothPresheaf n).germ (X := TopCat.of (RealN n)) ⟨U, hU⟩ x hxU s)
      = sectionToSmoothGerm n x U hU hxU s := by
  dsimp [stalkToSmoothGerm, stalkToSmoothGermHom, TopCat.Presheaf.germ]
  exact colimit.ι_desc_apply (smoothGermCocone n x) (op ⟨⟨U, hU⟩, hxU⟩) s

/-- Helper: if two sections over open neighbourhoods of `x` give rise to the
same smooth germ at `x`, then they give the same element of the stalk.

This is the "injectivity-on-germs" property that lets us conclude both inverse
identities for the equivalence `stalk ≃ SmoothGerm`. -/
lemma germ_eq_of_sectionToSmoothGerm_eq (n : ℕ) (x : RealN n)
    {U₁ U₂ : Set (RealN n)} (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂)
    (hx₁ : x ∈ U₁) (hx₂ : x ∈ U₂)
    (s₁ : SmoothSections n U₁) (s₂ : SmoothSections n U₂)
    (h : sectionToSmoothGerm n x U₁ hU₁ hx₁ s₁ = sectionToSmoothGerm n x U₂ hU₂ hx₂ s₂) :
    (smoothPresheaf n).germ (X := TopCat.of (RealN n)) ⟨U₁, hU₁⟩ x hx₁ s₁
      = (smoothPresheaf n).germ (X := TopCat.of (RealN n)) ⟨U₂, hU₂⟩ x hx₂ s₂ := by
  -- Reduce to representatives `f₁, f₂ : SmoothFun n Uᵢ`.
  induction s₁ using Quot.ind with
  | _ f₁ =>
    induction s₂ using Quot.ind with
    | _ f₂ =>
      -- From the equality of smooth germs, extract eventual equality of the
      -- underlying functions in the neighbourhood filter of `x`.
      have hfun : (f₁.toFun : Filter.Germ (𝓝 x) ℝ) = (f₂.toFun : Filter.Germ (𝓝 x) ℝ) := by
        simpa [sectionToSmoothGerm] using congrArg Subtype.val h
      -- Find an open `W ⊆ U₁ ∩ U₂` containing `x` on which the functions agree.
      obtain ⟨S, hS, hSeq⟩ :=
        Filter.eventuallyEq_iff_exists_mem.mp (Filter.Germ.coe_eq.mp hfun)
      obtain ⟨V, hVS, hVopen, hxV⟩ := mem_nhds_iff.mp hS
      set W : Set (RealN n) := V ∩ U₁ ∩ U₂
      have hWopen : IsOpen W := (hVopen.inter hU₁).inter hU₂
      have hxW : x ∈ W := ⟨⟨hxV, hx₁⟩, hx₂⟩
      have hWU₁ : W ⊆ U₁ := fun _ ⟨⟨_, hyU₁⟩, _⟩ => hyU₁
      have hWU₂ : W ⊆ U₂ := fun _ ⟨_, hyU₂⟩ => hyU₂
      -- Build the corresponding inclusions of opens (no `let` to keep
      -- everything flat for `rw` to find).
      have hWU₁hom : (⟨W, hWopen⟩ : Opens (RealN n)) ⟶ ⟨U₁, hU₁⟩ := homOfLE hWU₁
      have hWU₂hom : (⟨W, hWopen⟩ : Opens (RealN n)) ⟶ ⟨U₂, hU₂⟩ := homOfLE hWU₂
      -- Both sections, after restricting to `W`, become the same quot class.
      have hrestrict_eq :
          (smoothPresheaf n).map hWU₁hom.op (Quot.mk _ f₁)
            = (smoothPresheaf n).map hWU₂hom.op (Quot.mk _ f₂) := by
        -- The map of the presheaf is `SmoothSections.restrict`; both sides
        -- become `Quot.mk _ ⟨_, _⟩` of the restricted functions; they agree
        -- on `W` so the quotient classes coincide.
        rw [smoothPresheaf_map_mk, smoothPresheaf_map_mk]
        exact Quot.sound fun _ ⟨⟨hyV, _⟩, _⟩ => hSeq (hVS hyV)
      exact ((smoothPresheaf n).germ_res_apply hWU₁hom x hxW _).symm.trans
        ((congrArg _ hrestrict_eq).trans ((smoothPresheaf n).germ_res_apply hWU₂hom x hxW _))

/-- `smoothGermToStalk g` is the germ of a section whose smooth germ is `g`. -/
private theorem exists_germ_eq_smoothGermToStalk (n : ℕ) (x : RealN n) (g : SmoothGerm n x) :
    ∃ (U : Set (RealN n)) (hU : IsOpen U) (hxU : x ∈ U) (s : SmoothSections n U),
      sectionToSmoothGerm n x U hU hxU s = g ∧
        smoothGermToStalk n x g
          = (smoothPresheaf n).germ (X := TopCat.of (RealN n)) ⟨U, hU⟩ x hxU s := by
  unfold smoothGermToStalk
  set h := exists_smoothGermWitness n x g
  exact ⟨_, _, _, _, h.choose_spec.choose_spec.choose_spec.choose_spec, rfl⟩

/-- Right inverse: applying the forward map to the output of the backward map
recovers the original smooth germ. -/
lemma stalkToSmoothGerm_smoothGermToStalk (n : ℕ) (x : RealN n)
    (g : SmoothGerm n x) :
    stalkToSmoothGerm n x (smoothGermToStalk n x g) = g := by
  obtain ⟨U, hU, hxU, s, hs, he⟩ := exists_germ_eq_smoothGermToStalk n x g
  rw [he, stalkToSmoothGerm_germ_apply, hs]

/-- Left inverse: applying the backward map to the output of the forward map
recovers the original stalk element. -/
lemma smoothGermToStalk_stalkToSmoothGerm (n : ℕ) (x : RealN n)
    (t : (smoothPresheaf n).stalk (X := TopCat.of (RealN n)) x) :
    smoothGermToStalk n x (stalkToSmoothGerm n x t) = t := by
  -- Every stalk element is the germ of a section.
  obtain ⟨⟨U, hU⟩, hxU, s, ht⟩ := (smoothPresheaf n).exists_germ_eq
    (X := TopCat.of (RealN n)) t
  subst ht
  rw [stalkToSmoothGerm_germ_apply n x U hU hxU s]
  obtain ⟨_, _, _, _, hs, he⟩ :=
    exists_germ_eq_smoothGermToStalk n x (sectionToSmoothGerm n x U hU hxU s)
  exact he.trans (germ_eq_of_sectionToSmoothGerm_eq n x _ hU _ hxU _ s hs)

/-- **Main theorem (Stacks 007C).** For `X = ℝ^n` with the Euclidean topology
and `C^∞_{ℝ^n}` the presheaf of `C^∞` real-valued functions, the stalk at a
point `x ∈ ℝ^n` is in bijection with the type of smooth germs at `x`, that is,
equivalence classes of `C^∞` functions defined on open neighbourhoods of `x`
modulo eventual equality. -/
@[stacks 007C]
noncomputable def stalkEquivSmoothGerm (n : ℕ) (x : RealN n) :
    (smoothPresheaf n).stalk (X := TopCat.of (RealN n)) x ≃ SmoothGerm n x where
  toFun := stalkToSmoothGerm n x
  invFun := smoothGermToStalk n x
  left_inv := smoothGermToStalk_stalkToSmoothGerm n x
  right_inv := stalkToSmoothGerm_smoothGermToStalk n x

/-- Characterization of smooth germs: a germ in `Filter.Germ (𝓝 x) ℝ` is a
smooth germ iff it admits a representative `f` defined on a set whose interior
contains `x` and on which `f` is `C^∞`. -/
theorem isSmoothGerm_iff (n : ℕ) (x : RealN n) (g : Filter.Germ (𝓝 x) ℝ) :
    IsSmoothGerm n x g ↔
      ∃ f : RealN n → ℝ, ∃ s : Set (RealN n), x ∈ interior s ∧
        ContDiffOn ℝ ⊤ f s ∧ g = (f : Filter.Germ (𝓝 x) ℝ) := by
  constructor
  · rintro ⟨U, hU, hxU, f, hf, hg⟩
    exact ⟨f, U, by rwa [hU.interior_eq], hf, hg⟩
  · rintro ⟨f, s, hx, hf, hg⟩
    obtain ⟨U, hUs, hUopen, hxU⟩ := mem_interior.mp hx
    exact ⟨U, hUopen, hxU, f, hf.mono hUs, hg⟩

/-- Two function representatives determine the same germ at `x` iff they are
eventually equal in the neighbourhood filter of `x`.  Applied to smooth
representatives, this is the identification of germs in the stalk. -/
theorem smoothGerm_eq_iff (n : ℕ) (x : RealN n) (f₁ f₂ : RealN n → ℝ) :
    (f₁ : Filter.Germ (𝓝 x) ℝ) = (f₂ : Filter.Germ (𝓝 x) ℝ) ↔ f₁ =ᶠ[𝓝 x] f₂ :=
  Filter.Germ.coe_eq

