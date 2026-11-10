module

import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.Parity
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.Data.NNRat.Floor
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.Topology.Sheaves.Init
import Mathlib.CategoryTheory.Limits.Shapes.Connected
import Mathlib.CategoryTheory.Monoidal.Mon

public import StacksFrontier.CategoryTheory.Sites.Localization.StacksAndLocalization
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PushforwardStack
public import StacksFrontier.CategoryTheory.Sites.Stack.Transport.StackTransport
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver

/-!
# Construction B of Stacks 04WV
-/

@[expose] public section

namespace CategoryTheory

open Limits

universe w v₁ v₂ u₁ u₂

namespace Over

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {U : 𝒞}

/-- Two objects of `𝒞/U` with the same underlying object of `𝒞` and the same structure morphism
are equal. -/
lemma over_ext {A B : Over U} (h : A.left = B.left) (hh : A.hom = eqToHom h ≫ B.hom) : A = B :=
  CostructuredArrow.obj_ext A B h (by simpa using hh.symm)

/-- Two sections of `h_U` over `A.left`, for `A` an object of `𝒞/U`, that agree after restriction
along the members of a `J.over U`-covering sieve of `A` agree, when `h_U` is a sheaf: by
`CategoryTheory.Sieve.overEquiv` the members of the sieve correspond to the members of a
`J`-covering sieve of `A.left` in `𝒞`, and a sheaf is separated. -/
lemma section_eq_of_locally_eq {J : GrothendieckTopology 𝒞}
    (hU : Presieve.IsSheaf J (yoneda.obj U)) {A : Over U} (S : Sieve A)
    (hS : S ∈ (J.over U) A) {c d : A.left ⟶ U}
    (h : ∀ ⦃B : Over U⦄ ⦃k : B ⟶ A⦄, S k → k.left ≫ c = k.left ≫ d) : c = d := by
  refine (hU _ ((J.mem_over_iff S).1 hS)).isSeparatedFor.ext fun Y k hk ↦ ?_
  simpa using h ((Sieve.overEquiv_iff S k).1 hk)

/-- Restriction of a pair of sections of `h_U` along a morphism that factors through another:
if the two agree after restriction along `f`, they agree after restriction along `g ≫ f`. -/
lemma restrict_eq_of_comp {A B C : Over U} (g : B ⟶ C) (f : C ⟶ A) {c d : A.left ⟶ U}
    (h : f.left ≫ c = f.left ≫ d) : (g ≫ f).left ≫ c = (g ≫ f).left ≫ d := by
  rw [Over.comp_left, Category.assoc, h, Category.assoc]

/-- `CategoryTheory.Over.section_eq_of_locally_eq` for a covering *family* rather than a covering
sieve: it is enough that the two sections agree after restriction along each member of a family
generating a `J.over U`-covering sieve, the members of the generated sieve being the morphisms
factoring through one of the `fᵢ`. -/
lemma section_eq_of_locally_eq_ofArrows {J : GrothendieckTopology 𝒞}
    (hU : Presieve.IsSheaf J (yoneda.obj U)) {A : Over U} {ι : Type w} (Aᵢ : ι → Over U)
    (fᵢ : (i : ι) → Aᵢ i ⟶ A) (hcov : Sieve.generate (Presieve.ofArrows Aᵢ fᵢ) ∈ (J.over U) A)
    {c d : A.left ⟶ U} (h : ∀ i, (fᵢ i).left ≫ c = (fᵢ i).left ≫ d) : c = d := by
  refine section_eq_of_locally_eq hU _ hcov ?_
  rintro B k ⟨W, g, f, ⟨i⟩, rfl⟩
  exact restrict_eq_of_comp g (fᵢ i) (h i)

section ConstructionB

variable {𝒮 : Type u₂} [Category.{v₂} 𝒮]

/-- **The pushforward `j_U^q 𝒮` of Stacks 04WB**, for `q = p ⋙ j_U` the composite of
`p : 𝒮 ⥤ 𝒞/U` with the localization functor: its objects are the pairs of an object `A` of `𝒞/U`
and an object `y` of `𝒮` with `q y = A.left` on the nose, and its morphisms the pairs of a
morphism of `𝒞/U` and a morphism of `𝒮` lying over it. -/
abbrev SlicePush (p : 𝒮 ⥤ Over U) := StrictPullback (Over.forget U) (p ⋙ Over.forget U)

/-- The structure functor `j_U^q 𝒮 ⥤ 𝒞/U` of the pushforward, `(A, y) ↦ A`. -/
abbrev slicePush (p : 𝒮 ⥤ Over U) : SlicePush p ⥤ Over U :=
  StrictPullback.structureFunctor (Over.forget U) (p ⋙ Over.forget U)

/-- The section of `h_U` carried by the fibre component of an object of `j_U^q 𝒮`: the object
`X.fib` of `𝒮` lies over an object `p X.fib` of `𝒞/U` whose underlying object of `𝒞` is
`X.base.left`, and `sliceSec` is its structure morphism to `U`, read on `X.base.left`.

An object of `j_U^q 𝒮` therefore carries *two* sections of `h_U` over `X.base.left`: this one and
`X.base.hom`. They need not agree, and the full subcategory on which they do is the image of `𝒮`
(`CategoryTheory.Over.LiesOverSlice`). -/
def sliceSec (p : 𝒮 ⥤ Over U) (X : SlicePush p) :
    X.base.left ⟶ U :=
  eqToHom X.over.symm ≫ (p.obj X.fib).hom

/-- The two sections of `h_U` carried by an object of `j_U^q 𝒮` are compatible with morphisms:
`sliceSec` restricts along the `𝒞/U`-component of a morphism. -/
lemma sliceSec_comp (p : 𝒮 ⥤ Over U)
    {X Y : SlicePush p} (f : X ⟶ Y) :
    f.base.left ≫ sliceSec p Y = sliceSec p X := by
  have hw : (p.map f.fib).left ≫ (p.obj Y.fib).hom = (p.obj X.fib).hom := Over.w (p.map f.fib)
  have hf : (p.map f.fib).left = eqToHom X.over ≫ f.base.left ≫ eqToHom Y.over.symm := f.over
  simp [sliceSec, ← hw, hf, Category.assoc]

/-- **The objects of `j_U^q 𝒮` coming from `𝒮`.** An object of the pushforward `j_U^q 𝒮` is a pair
of an object `A` of `𝒞/U` and an object `y` of `𝒮` with `(p y).left = A.left`; it comes from `𝒮`
exactly when moreover the two structure morphisms to `U` agree, that is when `p y = A`. This is the
property cutting out the full subcategory of Stacks 04TU used by Construction B. -/
@[implicit_reducible]
def LiesOverSlice (p : 𝒮 ⥤ Over U) :
    ObjectProperty (SlicePush p) :=
  fun X => p.obj X.fib = X.base

/-- `LiesOverSlice` says exactly that the two sections of `h_U` carried by an object agree. -/
lemma liesOverSlice_iff (p : 𝒮 ⥤ Over U)
    (X : SlicePush p) :
    LiesOverSlice p X ↔ sliceSec p X = X.base.hom := by
  obtain ⟨B, y, ho⟩ := X
  constructor
  · intro hX
    obtain rfl : p.obj y = B := hX
    simp [sliceSec]
  · intro hX
    exact over_ext ho (by rw [← hX]; simp [sliceSec])

/-- The source of a morphism whose target comes from `𝒮` comes from `𝒮`: the structure morphism to
`U` of an object of `𝒮` is determined by any morphism out of it. In particular `LiesOverSlice` is
closed under isomorphism, and — with no cartesianness needed — under pullback. -/
lemma liesOverSlice_of_hom (p : 𝒮 ⥤ Over U)
    {X Y : SlicePush p} (f : X ⟶ Y)
    (hY : LiesOverSlice p Y) : LiesOverSlice p X := by
  rw [liesOverSlice_iff] at hY ⊢
  rw [← sliceSec_comp p f, hY, Over.w f.base]

/-- For `LiesOverSlice` the fibrewise reading of "isomorphic to an object of the subcategory" is
the property itself. -/
lemma liesOverSlice_of_isoOverId (p : 𝒮 ⥤ Over U)
    {X : SlicePush p}
    (h : Functor.IsoOverId (slicePush p) (LiesOverSlice p) X) : LiesOverSlice p X := by
  obtain ⟨Y, hY, e, -⟩ := h
  exact liesOverSlice_of_hom p e.hom hY

/-- **Condition (1) of Stacks 04TU for `LiesOverSlice`**: the subcategory is closed under
pullback. Nothing is used but the existence of the morphism `f^* X ⟶ X`; cartesianness is not
needed, and neither is the sheaf hypothesis. -/
lemma closedUnderStronglyCartesian_liesOverSlice (p : 𝒮 ⥤ Over U) :
    Functor.ClosedUnderStronglyCartesian (slicePush p) (LiesOverSlice p) :=
  fun _ φ _ hX ↦ Functor.isoOverId_of_prop (liesOverSlice_of_hom p φ hX)

/-- **Condition (3) of Stacks 04TU for `LiesOverSlice`**: the subcategory is local on the base.
**This is where the hypothesis of Stacks 04WV is used.** -/
lemma locallyClosed_liesOverSlice (p : 𝒮 ⥤ Over U) {J : GrothendieckTopology 𝒞}
    (hU : Presieve.IsSheaf J (yoneda.obj U)) [(slicePush p).IsPreFibered] :
    Functor.LocallyClosed (slicePush p) (LiesOverSlice p) (J.over U) := by
  intro A ι Aᵢ fᵢ hcov x hpull
  obtain ⟨X, rfl⟩ := x
  refine Functor.isoOverId_of_prop ((liesOverSlice_iff p X).2 ?_)
  refine section_eq_of_locally_eq_ofArrows hU Aᵢ fᵢ hcov ?_
  intro i
  set φ := Functor.IsPreFibered.pullbackMap
    (⟨X, rfl⟩ : (slicePush p).Fiber _).2 (fᵢ i)
  -- `(pullbackFiber …).1` is the chosen pullback object, which is the source of `φ`.
  have hYP : LiesOverSlice p
      (Functor.IsPreFibered.pullbackObj (⟨X, rfl⟩ : (slicePush p).Fiber _).2 (fᵢ i)) :=
    liesOverSlice_of_isoOverId p (hpull i)
  have star : φ.base.left ≫ sliceSec p X = φ.base.left ≫ X.base.hom := by
    rw [sliceSec_comp p φ, (liesOverSlice_iff p _).1 hYP, Over.w φ.base]
  -- `φ` lies over `fᵢ i`, so `fᵢ i` is `φ.base` up to the comparison of the two names for its
  -- source, and the two sections agree along `φ.base` by `star`.
  have hfac := CategoryTheory.IsHomLift.fac (slicePush p) (fᵢ i) φ
  rw [eqToHom_refl, Category.comp_id] at hfac
  rw [hfac]
  exact restrict_eq_of_comp _ _ star

/-! ### The image of `𝒮` in the pushforward

`𝒮` is isomorphic, as a category over `𝒞/U`, to the full subcategory of the pushforward `j_U^q 𝒮`
cut out by `CategoryTheory.Over.LiesOverSlice`: the comparison functor `y ↦ (p y, y)` is bijective
on objects and fully faithful, with inverse `(A, y) ↦ y`. -/

/-- **The comparison functor of Construction B**, `𝒮 ⥤ j_U^q 𝒮`: an object `y` of `𝒮` goes to the
object `(p y, y)` of the pushforward, which lies in the full subcategory
`CategoryTheory.Over.LiesOverSlice` because its two sections of `h_U` agree on the nose. -/
@[simps, implicit_reducible]
def toSliceFullSub (p : 𝒮 ⥤ Over U) : 𝒮 ⥤ (LiesOverSlice p).FullSubcategory where
  obj y := ⟨⟨p.obj y, y, rfl⟩, rfl⟩
  map φ := ObjectProperty.homMk { base := p.map φ, fib := φ, «over» := by simp }
  map_id y := by
    apply ObjectProperty.hom_ext
    refine StrictPullback.Hom.ext ?_ ?_ <;> simp
  map_comp φ ψ := by
    apply ObjectProperty.hom_ext
    refine StrictPullback.Hom.ext ?_ ?_ <;> simp

/-- The inverse of `CategoryTheory.Over.toSliceFullSub`: an object of the pushforward coming from
`𝒮` is remembered by its `𝒮`-component alone, the `𝒞/U`-component being `p` of it. -/
@[simps, implicit_reducible]
def fromSliceFullSub (p : 𝒮 ⥤ Over U) : (LiesOverSlice p).FullSubcategory ⥤ 𝒮 where
  obj X := X.obj.fib
  map f := f.hom.fib

/-- `CategoryTheory.Over.toSliceFullSub` is a functor over `𝒞/U`. -/
lemma toSliceFullSub_comp_restrict (p : 𝒮 ⥤ Over U) :
    toSliceFullSub p ⋙ Functor.restrict (slicePush p) (LiesOverSlice p) = p :=
  rfl

/-- `CategoryTheory.Over.fromSliceFullSub` is a functor over `𝒞/U`. Unlike
`CategoryTheory.Over.toSliceFullSub_comp_restrict` this is not an identity: it is exactly the
property cutting out the subcategory. -/
lemma fromSliceFullSub_comp (p : 𝒮 ⥤ Over U) :
    fromSliceFullSub p ⋙ p = Functor.restrict (slicePush p) (LiesOverSlice p) := by
  refine Functor.ext (fun X ↦ X.property) fun X Y f ↦ ?_
  ext
  simpa using f.hom.over

/-- One round trip of the comparison is the identity on the nose. -/
lemma toSliceFullSub_comp_fromSliceFullSub (p : 𝒮 ⥤ Over U) :
    toSliceFullSub p ⋙ fromSliceFullSub p = 𝟭 𝒮 :=
  rfl

/-- The other round trip of the comparison is the identity: an object of the pushforward lying in
the subcategory is rebuilt from its `𝒮`-component, since its `𝒞/U`-component is then `p` of it. -/
lemma fromSliceFullSub_comp_toSliceFullSub (p : 𝒮 ⥤ Over U) :
    fromSliceFullSub p ⋙ toSliceFullSub p = 𝟭 (LiesOverSlice p).FullSubcategory := by
  have hobj : ∀ X : (LiesOverSlice p).FullSubcategory,
      (fromSliceFullSub p ⋙ toSliceFullSub p).obj X = X := by
    rintro ⟨⟨B, y, ho⟩, hX⟩
    obtain rfl : p.obj y = B := hX
    rfl
  refine Functor.ext hobj ?_
  rintro ⟨⟨B, y, ho⟩, hX⟩ ⟨⟨C, z, ho'⟩, hY⟩ f
  obtain rfl : p.obj y = B := hX
  obtain rfl : p.obj z = C := hY
  obtain rfl : ho = rfl := rfl
  obtain rfl : ho' = rfl := rfl
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply ObjectProperty.hom_ext
  refine StrictPullback.Hom.ext ?_ ?_
  · ext
    simpa using f.hom.over
  · rfl

end ConstructionB

/-- **Construction B of Stacks 04WV, at the level of stacks.** Let `U` be an object of `𝒞` whose
representable presheaf `h_U` is a sheaf, and let `p : 𝒮 ⥤ 𝒞/U` be a functor whose composite with
the localization functor `j_U` is a stack over `(𝒞, J)`. Then `p` itself is a stack over the site
`(𝒞/U, J.over U)`. This is the source's "in this case it is automatically the case that
`p : 𝒯 → 𝒞/U` is a stack over `𝒞/U`".

The proof is by reduction to three results rather than by a clause-by-clause verification:

* the pushforward `j_U^q 𝒮` of `q = p ⋙ j_U` along `j_U` is a stack over `(𝒞/U, J.over U)`, by
  Stacks 04WC (`CategoryTheory.StrictPullback.isStack_structureFunctor`), `j_U` being a continuous
  functor of sites;
* the full subcategory of `j_U^q 𝒮` cut out by `CategoryTheory.Over.LiesOverSlice` is a stack, by
  Stacks 04TU (`CategoryTheory.Functor.IsStack.fullSubcategory`); **this is the only place the
  hypothesis that `h_U` is a sheaf is used**, in
  `CategoryTheory.Over.locallyClosed_liesOverSlice`;
* `𝒮` is isomorphic to that full subcategory as a category over `𝒞/U`, so it is a stack by
  Stacks 042W (`CategoryTheory.BasedCategory.Equivalence.isStack`).

Two costs of this route, both stated here rather than hidden.

* It carries the hypothesis `[HasPullbacks 𝒞]`, which Stacks 04WV does not. It is inherited from
  Stacks 04WC, whose proof genuinely uses fibre products in the source site
  (`CategoryTheory.StrictPullback.glue`); the source's notion of a morphism of sites (Stacks 00WU)
  asks for them, and Mathlib's `Functor.IsContinuous` does not. So this is Construction B for a
  site with fibre products, which is a mild weakening of 04WV.
* The universes are *not* pinned, and the earlier note here saying they were is superseded. The
  pushforward lives in `Type (max u₁ v₁ u₂)` with morphisms in `max v₁ v₂`, and `𝒮` used to be
  given there so that it and the full subcategory of the pushforward coincide; but the transport
  of the stack condition does not need that, because `CategoryTheory.BasedCategory.Equivalence`
  and Stacks 042W relate two categories over `𝒞` in independent object and morphism universes
  (`CategoryTheory.BasedCategory.isStack_iff_of_equivalence`), and
  `CategoryTheory.Over.toSliceFullSub` and `CategoryTheory.Over.fromSliceFullSub` are already
  stated at the file's general `{𝒮 : Type u₂} [Category.{v₂} 𝒮]`. So the statement below is given
  at that generality. The previously pinned case is recompiled as an instance of it, at the two
  universe settings where it is used: `CategoryTheory.Over.isStack_map_iff` and
  `CategoryTheory.Over.isStack_of_comp_forget_slice` keep their own statements unchanged and only
  their explicit universe applications of this result move. -/
@[stacks 04WV]
theorem isStack_of_comp_forget [HasPullbacks 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮]
    (p : 𝒮 ⥤ Over U) {J : GrothendieckTopology 𝒞}
    (hU : Presheaf.IsSheaf J (yoneda.obj U)) (hq : (p ⋙ Over.forget U).IsStack J) :
    p.IsStack (J.over U) := by
  have h1 : Functor.IsStack (slicePush p) (J.over U) :=
    StrictPullback.isStack_structureFunctor (J.over U) J (Over.forget U) (p ⋙ Over.forget U) hq
  have : (slicePush p).IsPreFibered := h1.isFibered.toIsPreFibered
  have h2 : Functor.IsStack (Functor.restrict (slicePush p) (LiesOverSlice p)) (J.over U) :=
    Functor.IsStack.fullSubcategory (slicePush p) (J.over U) h1 (LiesOverSlice p)
      (closedUnderStronglyCartesian_liesOverSlice p)
      (locallyClosed_liesOverSlice p ((isSheaf_iff_isSheaf_of_type J _).1 hU))
  exact BasedCategory.Equivalence.isStack
    (𝒳 := BasedCategory.ofFunctor (Functor.restrict (slicePush p) (LiesOverSlice p)))
    (𝒴 := BasedCategory.ofFunctor p)
    { functor := { toFunctor := fromSliceFullSub p, w := fromSliceFullSub_comp p }
      inverse := { toFunctor := toSliceFullSub p, w := toSliceFullSub_comp_restrict p }
      unitIso := eqToIso (BasedCategory.BasedFunctor.ext' (fromSliceFullSub_comp_toSliceFullSub p))
      counitIso :=
        eqToIso (BasedCategory.BasedFunctor.ext' (toSliceFullSub_comp_fromSliceFullSub p)) }
    (J.over U) h2

/-- **A change of slice neither creates nor destroys the stack condition of Stacks 026F.** For a
morphism `g : V ⟶ W` of a site `(𝒞, J)` with a subcanonical topology, a category `p : 𝒮 ⥤ 𝒞/V` is
a stack over `(𝒞/V, J.over V)` exactly when `p ⋙ Over.map g` is a stack over `(𝒞/W, J.over W)`.

Both sides are read through the one statement `(p ⋙ Over.forget V).IsStack J` over the ambient
site, by Constructions A and B of Stacks 04WV: `CategoryTheory.Functor.isStack_comp_forget` in one
direction and `CategoryTheory.Over.isStack_of_comp_forget` in the other, at `V` for the right-hand
side and at `W` for the left-hand side, the two being matched by
`CategoryTheory.Over.mapForget_eq`. Subcanonicity is what supplies the sheaf hypothesis of those
two results for the representable presheaves of `V` and of `W`; the hypothesis `[HasPullbacks 𝒞]`
is inherited from Construction B. -/
theorem isStack_map_iff [HasPullbacks 𝒞] {V W : 𝒞} (g : V ⟶ W)
    {𝒮 : Type (max u₁ v₁ u₂)} [Category.{max v₁ v₂} 𝒮] (p : 𝒮 ⥤ Over V)
    {J : GrothendieckTopology 𝒞} [J.Subcanonical] :
    (p ⋙ Over.map g).IsStack (J.over W) ↔ p.IsStack (J.over V) := by
  have hsheaf (X : 𝒞) : Presheaf.IsSheaf J (yoneda.obj X) :=
    (isSheaf_iff_isSheaf_of_type J _).2
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (yoneda.obj X))
  have hcomp : (p ⋙ Over.map g) ⋙ Over.forget W = p ⋙ Over.forget V := by
    rw [Functor.assoc, Over.mapForget_eq]
  constructor
  · intro h
    refine Over.isStack_of_comp_forget.{v₁, max v₁ v₂, u₁, max u₁ v₁ u₂} p (hsheaf V) ?_
    rw [← hcomp]
    exact Functor.isStack_comp_forget (p ⋙ Over.map g) (hsheaf W) h
  · intro h
    refine Over.isStack_of_comp_forget.{v₁, max v₁ v₂, u₁, max u₁ v₁ u₂} (p ⋙ Over.map g)
      (hsheaf W) ?_
    rw [hcomp]
    exact Functor.isStack_comp_forget p (hsheaf V) h

/-! ### Constructions A and B as mutually inverse functors of the 2-categories of stacks

`StacksFrontier/CategoryTheory/Sites/Localization/StacksAndLocalization.lean` has Construction A
as a functor of the 2-categories of stacks, bijective on 1-morphisms and on 2-morphisms and
compatible with identities, composition and whiskering
(`CategoryTheory.Over.stackConstructionHomEquiv`, `CategoryTheory.Over.stackConstructionHom₂Equiv`
and their companions). Construction B completes it to a bijection on objects, and that is all of
Stacks 04WV that was missing.

The universes are pinned exactly as there, and for the same reason: the right-hand 2-category
speaks of a 1-morphism `𝒯 ⟶ 𝒞/U` inside the 2-category of stacks over `𝒞`, so `𝒞/U` has to be an
object of that 2-category, which forces the fibre universes to be `𝒞/U`'s own. -/

section TwoCategory

variable (U) [HasPullbacks 𝒞] (J : GrothendieckTopology 𝒞)
  (hU : Presheaf.IsSheaf J (yoneda.obj U))

-- Every declaration below is a statement about `hU`, but two of them mention it only in
-- their proofs.
include hU

/-- `CategoryTheory.Over.isStack_of_comp_forget` in the universe setting of the 2-category of
stacks over `𝒞`, where the fibre universes are those of `𝒞/U` itself. -/
theorem isStack_of_comp_forget_slice {𝒮 : Type (max u₁ v₁)} [Category.{v₁} 𝒮] (p : 𝒮 ⥤ Over U)
    (hq : (p ⋙ Over.forget U).IsStack J) : p.IsStack (J.over U) :=
  isStack_of_comp_forget.{v₁, v₁, u₁, max u₁ v₁} p hU hq

/-- Construction B for the data of a pair `(𝒯, p)`, with the structure functor of `𝒯` given as a
variable so that the equality `p ⋙ j_U = q` can be substituted. -/
lemma isStack_of_pair_aux {X₀ : Type (max u₁ v₁)} [Category.{v₁} X₀] (G : X₀ ⥤ Over U)
    (q : X₀ ⥤ 𝒞) (hw : G ⋙ Over.forget U = q) (hq : q.IsStack J) : G.IsStack (J.over U) := by
  subst hw
  exact isStack_of_comp_forget_slice U J hU G hq

/-- **Construction B of Stacks 04WV**, on objects: a pair `(𝒯, p)` consisting of a stack `𝒯` over
`(𝒞, J)` and a 1-morphism `p : 𝒯 ⟶ 𝒞/U` of stacks over `𝒞` is sent to `p : 𝒯 ⥤ 𝒞/U`, which is a
stack over `(𝒞/U, J.over U)` by `CategoryTheory.Over.isStack_of_comp_forget`. -/
def stackConstructionB (X : StackPair U J hU) :
    BasedStack.{v₁, v₁, max u₁ v₁, max u₁ v₁} (Over U) (J.over U) :=
  ⟨{ obj := X.1.toBasedCategory.obj, category := X.1.toBasedCategory.category,
      p := (X.2.hom.toFunctor : X.1.toBasedCategory.obj ⥤ Over U) },
    isStack_of_pair_aux U J hU (X.2.hom.toFunctor : X.1.toBasedCategory.obj ⥤ Over U)
      X.1.toBasedCategory.p X.2.hom.w X.1.isStack⟩

/-- The round trip `A ∘ B`, with the data of a pair spelled out so that the equality
`G ⋙ j_U = q` can be substituted: it identifies the structure functor of `𝒯` with `G ⋙ j_U`, after
which the two pairs are literally the same. -/
lemma stackConstructionA_stackConstructionB_aux {X₀ : Type (max u₁ v₁)} [instX : Category.{v₁} X₀]
    (G : X₀ ⥤ Over U) (q : X₀ ⥤ 𝒞) (hw : G ⋙ Over.forget U = q) (hq : q.IsStack J)
    (hmor : Functor.IsFibredOneMorphism q (Over.forget U) G) :
    stackConstructionA U J hU
        (stackConstructionB U J hU ⟨⟨⟨X₀, instX, q⟩, hq⟩, ⟨⟨G, hw⟩, hmor⟩⟩) =
      ⟨⟨⟨X₀, instX, q⟩, hq⟩, ⟨⟨G, hw⟩, hmor⟩⟩ := by
  subst hw
  rfl

/-- **Constructions A and B of Stacks 04WV are mutually inverse on objects.** A pair `(𝒯, p)`
carries no information beyond `p`, because "`p` is a 1-morphism of categories over `𝒞`" says
exactly that the structure functor of `𝒯` is `p ⋙ j_U`; and the two stack conditions agree, by
`CategoryTheory.Functor.isStack_comp_forget` in one direction and
`CategoryTheory.Over.isStack_of_comp_forget` in the other.

Together with `CategoryTheory.Over.stackConstructionHomEquiv` and
`CategoryTheory.Over.stackConstructionHom₂Equiv`, which are bijections on 1-morphisms and on
2-morphisms compatible with identities, composition and whiskering, this exhibits Constructions A
and B as mutually inverse functors of the two 2-categories. -/
@[stacks 04WV]
def stackConstructionObjEquiv :
    BasedStack.{v₁, v₁, max u₁ v₁, max u₁ v₁} (Over U) (J.over U) ≃ StackPair U J hU where
  toFun := stackConstructionA U J hU
  invFun := stackConstructionB U J hU
  left_inv _ := rfl
  right_inv X :=
    stackConstructionA_stackConstructionB_aux U J hU
      (X.2.hom.toFunctor : X.1.toBasedCategory.obj ⥤ Over U) X.1.toBasedCategory.p X.2.hom.w
      X.1.isStack X.2.isFibredOneMorphism

end TwoCategory

end Over

end CategoryTheory
