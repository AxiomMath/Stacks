module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.Functorial

/-!
# Separating points and tangent vectors

Let `k` be an algebraically closed field, let `f : X ⟶ Y` be a morphism of `k`-schemes, let `ℳ`
be a module on `Y` and let `θ : f^* ℳ ≅ ℒ` identify its pullback with a module `ℒ` on `X`. A
family of global sections of `ℳ`, transported to `ℒ` along `θ`, is said to *separate the closed
points* of `X` if for every ordered pair of distinct closed points one member of the family
vanishes at the first and not at the second, and to *separate tangent vectors* if for every
closed point and every nonzero tangent vector there one member of the family vanishes at the
point while its pullback along the tangent vector does not.

This file proves that the first condition makes `f` injective on `k`-points, that the second
makes every tangent map of `f` at a closed point injective, and that an injective-on-points,
proper, formally unramified morphism is a closed immersion. These are the three geometric steps
of the criterion of [Stacks, Tag 0E8S](https://stacks.math.columbia.edu/tag/0E8S) for a linear
system to define a closed immersion into projective space.

## Main definitions

* `AlgebraicGeometry.pullbackSectionTop` is the canonical map `Γ(Y, ℳ) → Γ(X, f^* ℳ)` on global
  sections induced by a morphism `f : X ⟶ Y`.
* `AlgebraicGeometry.VanishesAlong` says that a global section of a module on `X` pulls back to
  zero along a morphism into `X`. Taking the morphism to be the residue-field point of `x` is
  "vanishes at `x`"; taking it to be a dotted tangent arrow is "the pullback by the tangent
  vector is zero".
* `AlgebraicGeometry.SeparatesClosedPoints` is condition (1) of Tag 0E8S for a family of global
  sections.
* `AlgebraicGeometry.SeparatesTangentVectors` is condition (2) of Tag 0E8S for a family of
  global sections.

## Main results

* `AlgebraicGeometry.injective_of_separatesClosedPoints`: a family separating the closed points
  of `X`, whose members are pulled back from the target along `f`, forces `f` to be injective on
  `k`-points.
* `AlgebraicGeometry.tangentMap_injective_of_separatesTangentVectors`: a family separating the
  tangent vectors at a point `x`, whose members are pulled back along `f`, forces the tangent
  map of `f` at `x` to be injective.
* `AlgebraicGeometry.formallyUnramified_of_unramifiedAt_closedPoints`: a morphism out of a
  Jacobson scheme which is unramified at every closed point is formally unramified.
* `AlgebraicGeometry.mono_of_isProper_of_formallyUnramified` and
  `AlgebraicGeometry.isClosedImmersion_of_isProper_of_formallyUnramified`: over an algebraically
  closed field, a proper formally unramified morphism which is injective on `k`-points is a
  monomorphism, hence a closed immersion.
* `AlgebraicGeometry.isClosedImmersion_of_separatesClosedPoints`: the two previous items
  combined, so that condition (1) of Tag 0E8S plus formal unramifiedness gives a closed
  immersion.

## Which points are quantified over

The source quantifies conditions (1) and (2) of Tag 0E8S over the **closed points** of `X`, and
so do `AlgebraicGeometry.SeparatesClosedPoints` and
`AlgebraicGeometry.SeparatesTangentVectors` here; `IsClosed {x}` is the only form of the
condition used. For `X` locally of finite type over an algebraically closed field the closed
points correspond bijectively to the `k`-rational points, by Mathlib's
`AlgebraicGeometry.pointEquivClosedPoint`, and that equivalence is how
`AlgebraicGeometry.injective_of_separatesClosedPoints` is applied below; no statement here
quantifies over geometric points of a larger field.

## What is not proved here

Nothing in this file is registered as Tag 0E8S. The three geometric steps proved here
are assembled in the sibling file `SeparatingPointsTangentVectors/ClosedImmersion.lean`, where
condition (2) is converted into formal unramifiedness through
[Stacks, Tag 0B2G](https://stacks.math.columbia.edu/tag/0B2G); so
`AlgebraicGeometry.isClosedImmersion_of_separatesClosedPoints` below still takes formal
unramifiedness as a hypothesis, while the statements there derive it from condition (2).

Neither file produces the canonical morphism `φ_{ℒ,V} : X → 𝐏(V)` attached to a subspace
`V ⊂ H⁰(X, ℒ)` generating `ℒ`, nor the identification `φ_{ℒ,V}^* 𝒪(1) ≅ ℒ` — that is
[Stacks, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY). Both are supplied, from the two
separation conditions alone, in `SeparatingPointsTangentVectors/Canonical.lean`, which is where
Tag 0E8S is registered.

## A degenerate case in which the source statement fails

Tag 0E8S asserts its conclusion for an arbitrary subspace `V ⊂ H⁰(X, ℒ)` satisfying (1) and (2),
and its proof opens with "condition (1) implies in particular that the elements of `V` generate
`ℒ`". That implication needs `X` to have at least two closed points: for `X` with a single closed
point both (1) and (2) can hold while `V` generates nothing, and then `φ_{ℒ,V}` does not exist.
Two witnesses, both proper over `k`: `X = Spec k` with `ℒ = 𝒪_X` and `V = 0`, where (1) and (2)
are vacuous and `𝐏(V) = ∅`; and `X = Spec (k[t]/t²)` with `ℒ = 𝒪_X` and `V = k·t`, where (1) is
vacuous, (2) holds because `t` pulls back to a nonzero multiple of `ε` along every nonzero
tangent vector, and `t` lies in the maximal ideal so does not generate `ℒ` at the closed point.
Nothing below asserts that (1) implies generation, and no statement below depends on that
implication. In `SeparatingPointsTangentVectors/Canonical.lean` that implication appears as
`AlgebraicGeometry.generatesStalks_of_separatesClosedPoints`, guarded by the precise side
condition these two witnesses violate — that no closed point of `X` is its only one.

## References

* [Stacks Project, Tag 0E8S](https://stacks.math.columbia.edu/tag/0E8S)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe v u

namespace AlgebraicGeometry

/-! ### Global sections and pullback -/

section Sections

/-- The canonical map `Γ(Y, ℳ) → Γ(X, f^* ℳ)` on global sections attached to a morphism
`f : X ⟶ Y` and a module `ℳ` on `Y`, namely the unit of the pullback-pushforward adjunction
evaluated on the top open. -/
def pullbackSectionTop {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    M.val.obj (op ⊤) → ((Scheme.Modules.pullback f).obj M).val.obj (op ⊤) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app (op ⊤)

/-- A section of a module on `X` *vanishes along* a morphism `r : T ⟶ X` if it pulls back to the
zero section of `r^* ℒ`. Vanishing along the residue-field point of `x` is vanishing at `x`, and
vanishing along a dotted tangent arrow is vanishing of the pullback by that tangent vector. -/
def VanishesAlong {X T : Scheme.{u}} (r : T ⟶ X) {L : X.Modules} (s : L.val.obj (op ⊤)) : Prop :=
  pullbackSectionTop r L s = 0

/-- The component of the inverse of an isomorphism of modules on an open is injective. -/
lemma Scheme.Modules.inv_app_injective {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (U : (Opens X)ᵒᵖ) : Function.Injective (e.inv.val.app U) := by
  have h z : e.hom.val.app U (e.inv.val.app U z) = z := by
    have hz := congrArg (fun g => g.val.app U z) e.inv_hom_id
    change ((e.inv.val ≫ e.hom.val).app U) z = z at hz
    simpa [PresheafOfModules.comp_app, ModuleCat.comp_apply] using hz
  exact fun x y hxy =>
    (h x).symm.trans ((congrArg (fun z => e.hom.val.app U z) hxy).trans (h y))

/-- The component of an isomorphism of modules on an open is injective. -/
lemma Scheme.Modules.hom_app_injective {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (U : (Opens X)ᵒᵖ) : Function.Injective (e.hom.val.app U) :=
  Scheme.Modules.inv_app_injective e.symm U

/-- Pulling back global sections is natural in the module. -/
lemma pullbackSectionTop_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} (t : M ⟶ N) (s : M.val.obj (op ⊤)) :
    ((Scheme.Modules.pullback f).map t).val.app (op ⊤) (pullbackSectionTop f M s) =
      pullbackSectionTop f N (t.val.app (op ⊤) s) :=
  congr($((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality t).val.app (op ⊤)
    s).symm

/-- Pulling back global sections along a composite agrees, through the canonical isomorphism
`(f ≫ g)^* ≅ f^* g^*`, with pulling back twice. -/
lemma pullbackSectionTop_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (s : M.val.obj (op ⊤)) :
    ((Scheme.Modules.pullbackComp f g).inv.app M).val.app (op ⊤)
        (pullbackSectionTop (f ≫ g) M s) =
      pullbackSectionTop f ((Scheme.Modules.pullback g).obj M) (pullbackSectionTop g M s) := by
  have h := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  exact congr($(h).val.app (op ⊤) s).symm

/-- Pulling back global sections along equal morphisms agrees through the canonical isomorphism
of the two pullback functors. -/
lemma pullbackSectionTop_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (hfg : f = g)
    (M : Y.Modules) (s : M.val.obj (op ⊤)) :
    ((Scheme.Modules.pullbackCongr hfg).hom.app M).val.app (op ⊤) (pullbackSectionTop f M s) =
      pullbackSectionTop g M s := by
  subst g
  rfl

/-- Pulling back global sections along the identity recovers the section. -/
lemma pullbackSectionTop_id {X : Scheme.{u}} (M : X.Modules) (s : M.val.obj (op ⊤)) :
    ((Scheme.Modules.pullbackId X).hom.app M).val.app (op ⊤) (pullbackSectionTop (𝟙 X) M s) =
      s := by
  have h := unit_conjugateEquiv Adjunction.id
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X))
    (Scheme.Modules.pullbackId X).hom M
  rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at h
  exact congr($(h).val.app (op ⊤) s).symm

/-- A section vanishes along a composite exactly when its pullback along the second morphism
vanishes along the first. -/
lemma vanishesAlong_comp_iff {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (s : M.val.obj (op ⊤)) :
    VanishesAlong (f ≫ g) s ↔ VanishesAlong f (pullbackSectionTop g M s) := by
  rw [VanishesAlong, VanishesAlong, ← pullbackSectionTop_comp]
  exact (map_eq_zero_iff _ (Scheme.Modules.inv_app_injective
    ((Scheme.Modules.pullbackComp f g).app M) (op ⊤))).symm

/-- Vanishing along a morphism only depends on the morphism. -/
lemma vanishesAlong_congr_iff {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (M : Y.Modules) (s : M.val.obj (op ⊤)) :
    VanishesAlong f s ↔ VanishesAlong g s := by
  subst g
  rfl

/-- A section pulls back to zero along an isomorphism exactly when it is zero. -/
lemma vanishesAlong_iff_eq_zero {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (M : Y.Modules)
    (s : M.val.obj (op ⊤)) : VanishesAlong f s ↔ s = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ map_zero _⟩
  have hc : VanishesAlong (inv f ≫ f) s := by
    rw [vanishesAlong_comp_iff, VanishesAlong, h]
    exact map_zero _
  have hi : VanishesAlong (𝟙 Y) s := (vanishesAlong_congr_iff (IsIso.inv_hom_id f) M s).mp hc
  have hid := pullbackSectionTop_id M s
  rw [show pullbackSectionTop (𝟙 Y) M s = 0 from hi, map_zero] at hid
  exact hid.symm

/-- Let `θ : f^* ℳ ≅ ℒ` carry the pullback of `t : Γ(Y, ℳ)` to `s : Γ(X, ℒ)`. Then `t` vanishes
along `r ≫ f` exactly when `s` vanishes along `r`. -/
lemma vanishesAlong_comp_iff_of_pullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules}
    {L : X.Modules} (θ : (Scheme.Modules.pullback f).obj M ≅ L) {t : M.val.obj (op ⊤)}
    {s : L.val.obj (op ⊤)} (hts : θ.hom.val.app (op ⊤) (pullbackSectionTop f M t) = s)
    {T : Scheme.{u}} (r : T ⟶ X) : VanishesAlong (r ≫ f) t ↔ VanishesAlong r s := by
  rw [vanishesAlong_comp_iff]
  have hn := pullbackSectionTop_naturality r θ.hom (pullbackSectionTop f M t)
  rw [hts] at hn
  rw [VanishesAlong, VanishesAlong, ← hn]
  exact (map_eq_zero_iff _ (Scheme.Modules.hom_app_injective
    ((Scheme.Modules.pullback r).mapIso θ) (op ⊤))).symm

end Sections

/-! ### The separation conditions -/

section Separates

variable {X : Scheme.{u}} {L : X.Modules} {V : Type v}

/-- **Condition (1) of Stacks Project, Tag 0E8S.** A family of global sections of `ℒ` separates
the closed points of `X` if for every ordered pair of distinct closed points `x`, `y` some member
of the family vanishes at `x` but not at `y`. -/
def SeparatesClosedPoints (ψ : V → L.val.obj (op ⊤)) : Prop :=
  ∀ x y : X, IsClosed ({x} : Set X) → IsClosed ({y} : Set X) → x ≠ y →
    ∃ v : V, VanishesAlong (X.fromSpecResidueField x) (ψ v) ∧
      ¬ VanishesAlong (X.fromSpecResidueField y) (ψ v)

/-- **Condition (2) of Stacks Project, Tag 0E8S.** A family of global sections of `ℒ` separates
tangent vectors of `X` over `S` if for every closed point `x` and every nonzero tangent vector
`θ` at `x` some member of the family vanishes at `x` while its pullback by `θ` is nonzero. -/
def SeparatesTangentVectors {S : Scheme.{u}} (p : X ⟶ S) (ψ : V → L.val.obj (op ⊤)) : Prop :=
  ∀ x : X, IsClosed ({x} : Set X) → ∀ θ : DottedTangentArrow p x, θ ≠ 0 →
    ∃ v : V, VanishesAlong (X.fromSpecResidueField x) (ψ v) ∧ ¬ VanishesAlong θ.val (ψ v)

end Separates

/-! ### Residue fields at closed points -/

section ResidueField

/-- A section vanishes at a closed point of a scheme locally of finite type over an algebraically
closed field exactly when it vanishes along the corresponding rational point. -/
lemma vanishesAlong_pointOfClosedPoint_iff {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (x : X) (hx : IsClosed ({x} : Set X)) {L : X.Modules} (s : L.val.obj (op ⊤)) :
    VanishesAlong (pointOfClosedPoint p x hx) s ↔ VanishesAlong (X.fromSpecResidueField x) s := by
  rw [show pointOfClosedPoint p x hx =
    Spec.map (residueFieldIsoBase p x hx).hom ≫ X.fromSpecResidueField x from rfl,
    vanishesAlong_comp_iff, vanishesAlong_iff_eq_zero]
  exact Iff.rfl

/-- For a morphism whose composite with a morphism to an algebraically closed field is locally of
finite type, the residue-field homomorphism at a closed point is an isomorphism: both residue
fields are the base field. -/
lemma isIso_residueFieldMap_of_isClosed {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ Spec (.of k)) [LocallyOfFiniteType (f ≫ q)]
    (x : X) (hx : IsClosed ({x} : Set X)) : IsIso (f.residueFieldMap x) := by
  have he : Spec.preimage (Y.fromSpecResidueField (f x) ≫ q) ≫ f.residueFieldMap x =
      (residueFieldIsoBase (f ≫ q) x hx).inv := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc,
      SpecMap_residueFieldIsoBase_inv]
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨(f.residueFieldMap x).hom.injective, ?_⟩
  have hs := (ConcreteCategory.bijective_of_isIso
    (residueFieldIsoBase (f ≫ q) x hx).inv).surjective
  rw [← he] at hs
  exact Function.Surjective.of_comp hs

end ResidueField

/-! ### Injectivity on points from separation of closed points -/

section Points

/-- **The content of condition (1) of Stacks Project, Tag 0E8S.** Let `f : X ⟶ Y` be a morphism
of schemes with `X` locally of finite type over an algebraically closed field `k`, let
`θ : f^* ℳ ≅ ℒ` and let `ψ` be the family of global sections of `ℒ` obtained from a family `t` of
global sections of `ℳ` by pulling back along `f` and transporting along `θ`. If `ψ` separates the
closed points of `X`, then `f` is injective on `k`-points. -/
theorem injective_of_separatesClosedPoints {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    {M : Y.Modules} {L : X.Modules} (θ : (Scheme.Modules.pullback f).obj M ≅ L)
    {V : Type v} {t : V → M.val.obj (op ⊤)} {ψ : V → L.val.obj (op ⊤)}
    (htψ : ∀ v, θ.hom.val.app (op ⊤) (pullbackSectionTop f M (t v)) = ψ v)
    (hsep : SeparatesClosedPoints ψ) (a b : Spec (.of k) ⟶ X)
    (ha : a ≫ p = 𝟙 _) (hb : b ≫ p = 𝟙 _) (hab : a ≫ f = b ≫ f) : a = b := by
  by_contra hne
  set ea := (pointEquivClosedPoint p) ⟨a, ha⟩ with hea'
  set eb := (pointEquivClosedPoint p) ⟨b, hb⟩ with heb'
  have hea : pointOfClosedPoint p ea.1 ea.2 = a :=
    congrArg Subtype.val ((pointEquivClosedPoint p).symm_apply_apply ⟨a, ha⟩)
  have heb : pointOfClosedPoint p eb.1 eb.2 = b :=
    congrArg Subtype.val ((pointEquivClosedPoint p).symm_apply_apply ⟨b, hb⟩)
  have hxy : ea.1 ≠ eb.1 := fun h => hne (congrArg Subtype.val
    ((pointEquivClosedPoint p).injective (Subtype.ext h)))
  obtain ⟨v, hv, hw⟩ := hsep ea.1 eb.1 ea.2 eb.2 hxy
  refine hw ?_
  rw [← vanishesAlong_pointOfClosedPoint_iff p eb.1 eb.2, heb,
    ← vanishesAlong_comp_iff_of_pullbackIso f θ (htψ v) b, ← vanishesAlong_congr_iff hab,
    vanishesAlong_comp_iff_of_pullbackIso f θ (htψ v) a, ← hea,
    vanishesAlong_pointOfClosedPoint_iff p ea.1 ea.2]
  exact hv

end Points

/-! ### Injectivity of the tangent map from separation of tangent vectors -/

section Tangent

/-- The ring homomorphism `K[ε] →+* L[ε]` induced componentwise by a ring isomorphism
`K ≃+* L`. -/
def dualNumberRingHomOfRingEquiv {K L : Type u} [CommRing K] [CommRing L] (e : K ≃+* L) :
    DualNumber K →+* DualNumber L where
  toFun z := ⟨e z.fst, e z.snd⟩
  map_one' := by ext <;> simp
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · simp only [TrivSqZeroExt.fst_mul]
      exact map_mul e _ _
    · change e (x.fst * y.snd + x.snd * y.fst) = e x.fst * e y.snd + e x.snd * e y.fst
      simp only [map_add, map_mul]
  map_zero' := by ext <;> simp
  map_add' x y := TrivSqZeroExt.ext (map_add e x.fst y.fst) (map_add e x.snd y.snd)

/-- `dualNumberRingHomOfRingEquiv` is bijective. -/
lemma bijective_dualNumberRingHomOfRingEquiv {K L : Type u} [CommRing K] [CommRing L]
    (e : K ≃+* L) : Function.Bijective (dualNumberRingHomOfRingEquiv e) := by
  refine ⟨fun z w h => ?_, fun z => ⟨⟨e.symm z.fst, e.symm z.snd⟩, ?_⟩⟩
  · exact TrivSqZeroExt.ext (e.injective (congrArg TrivSqZeroExt.fst h))
      (e.injective (congrArg TrivSqZeroExt.snd h))
  · exact TrivSqZeroExt.ext (e.apply_symm_apply z.fst) (e.apply_symm_apply z.snd)

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (p : X ⟶ S) (q : Y ⟶ S)

omit q in
/-- If a section of `ℳ` vanishes along `r ≫ f` and a dotted tangent arrow `θ` at `x` becomes,
after pulling back along an isomorphism `a` of dual-number points, the constant arrow at the
residue-field point, then the pullback of the section along `θ` vanishes too. -/
lemma vanishesAlong_of_comp_eq_constant (x : X)
    (θ : DottedTangentArrow p x) (M : Y.Modules) (s : M.val.obj (op ⊤))
    (hs : VanishesAlong (X.fromSpecResidueField x ≫ f) s)
    (a : Spec (.of (DualNumber (Y.residueField (f x)))) ⟶
      Spec (.of (DualNumber (X.residueField x)))) [IsIso a]
    (hconst : a ≫ θ.val ≫ f =
      a ≫ (dualNumberToBase (X.residueField x) ≫ X.fromSpecResidueField x ≫ f)) :
    VanishesAlong θ.val (pullbackSectionTop f M s) := by
  have hcancel : θ.val ≫ f =
      dualNumberToBase (X.residueField x) ≫ X.fromSpecResidueField x ≫ f :=
    (cancel_epi a).mp hconst
  rw [← vanishesAlong_comp_iff, vanishesAlong_congr_iff hcancel,
    vanishesAlong_comp_iff _ (X.fromSpecResidueField x ≫ f), VanishesAlong,
    show pullbackSectionTop (X.fromSpecResidueField x ≫ f) M s = 0 from hs]
  exact map_zero _

omit q in
/-- A dual-number isomorphism realizing the residue-field identification at a point where the
residue-field homomorphism of `f` is an isomorphism. -/
lemma exists_bijective_dualNumberRingHom (x : X) [IsIso (f.residueFieldMap x)] :
    ∃ (α : DualNumber (X.residueField x) →+* DualNumber (Y.residueField (f x))),
      Function.Bijective α ∧
      (∀ z, TrivSqZeroExt.fst (α z) = (inv (f.residueFieldMap x)).hom (TrivSqZeroExt.fst z)) ∧
      (∀ z, TrivSqZeroExt.snd (α z) = (inv (f.residueFieldMap x)).hom (TrivSqZeroExt.snd z)) ∧
      (α.comp (algebraMap (X.residueField x) (DualNumber (X.residueField x)))).comp
          (f.residueFieldMap x).hom =
        algebraMap (Y.residueField (f x)) (DualNumber (Y.residueField (f x))) := by
  set e := (asIso (f.residueFieldMap x)).commRingCatIsoToRingEquiv with he
  refine ⟨dualNumberRingHomOfRingEquiv e.symm,
    bijective_dualNumberRingHomOfRingEquiv e.symm, fun _ => rfl, fun _ => rfl, ?_⟩
  ext z
  · change e.symm ((f.residueFieldMap x).hom z) = z
    change e.symm (e z) = z
    exact e.symm_apply_apply z
  · change e.symm 0 = 0
    exact map_zero _

/-- **The content of condition (2) of Stacks Project, Tag 0E8S.** Let `f : X ⟶ Y` be a morphism
over `S`, let `x` be a point of `X` at which the residue-field homomorphism of `f` is an
isomorphism, let `θ : f^* ℳ ≅ ℒ`, and let `ψ` be obtained from a family `t` of global sections of
`ℳ` by pulling back along `f` and transporting along `θ`. If `ψ` separates the tangent vectors
over `S` and `x` is closed, then the tangent map of `f` at `x` is injective. -/
theorem tangentMap_injective_of_separatesTangentVectors (h : f ≫ q = p)
    (x : X) (hx : IsClosed ({x} : Set X)) [IsIso (f.residueFieldMap x)]
    {M : Y.Modules} {L : X.Modules} (e : (Scheme.Modules.pullback f).obj M ≅ L)
    {V : Type v} {t : V → M.val.obj (op ⊤)} {ψ : V → L.val.obj (op ⊤)}
    (htψ : ∀ v, e.hom.val.app (op ⊤) (pullbackSectionTop f M (t v)) = ψ v)
    (hsep : SeparatesTangentVectors p ψ) :
    Function.Injective (tangentMap f p q h x) := by
  have key : ∀ θ : DottedTangentArrow p x, θ ≠ 0 → tangentMap f p q h x θ ≠ 0 := by
    intro θ hθ hzero
    obtain ⟨v, hvanish, hdetect⟩ := hsep x hx θ hθ
    obtain ⟨α, hαbij, hα₀, hα₁, hring⟩ := exists_bijective_dualNumberRingHom f x
    have : IsIso (CommRingCat.ofHom α) :=
      (ConcreteCategory.isIso_iff_bijective (CommRingCat.ofHom α)).mpr hαbij
    set a := Spec.map (CommRingCat.ofHom α) with ha
    have : IsIso a := by rw [ha]; infer_instance
    have hbase : a ≫ (dualNumberToBase (X.residueField x) ≫
          X.fromSpecResidueField x ≫ f) =
        dualNumberToBase (Y.residueField (f x)) ≫ Y.fromSpecResidueField (f x) := by
      rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
      simp only [ha, dualNumberToBase, ← Spec.map_comp_assoc]
      exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ) ≫
        Y.fromSpecResidueField (f x)) hring
    have hconst : a ≫ θ.val ≫ f =
        a ≫ (dualNumberToBase (X.residueField x) ≫ X.fromSpecResidueField x ≫ f) := by
      calc a ≫ θ.val ≫ f = (tangentMap f p q h x θ).val :=
            (tangentMap_apply f p q h x θ α hα₀ hα₁).symm
        _ = (0 : DottedTangentArrow q (f x)).val := congrArg Subtype.val hzero
        _ = dualNumberToBase (Y.residueField (f x)) ≫ Y.fromSpecResidueField (f x) :=
            (dottedTangentArrowModule q (f x)).zero_apply
        _ = _ := hbase.symm
    refine hdetect ?_
    rw [← vanishesAlong_comp_iff_of_pullbackIso f e (htψ v) θ.val]
    exact (vanishesAlong_comp_iff θ.val f M (t v)).mpr
      (vanishesAlong_of_comp_eq_constant f p x θ M (t v)
        ((vanishesAlong_comp_iff_of_pullbackIso f e (htψ v) (X.fromSpecResidueField x)).mpr
          hvanish) a hconst)
  intro θ η hθη
  by_contra hne
  exact key (θ - η) (sub_ne_zero.mpr hne) (by rw [map_sub, hθη, sub_self])

end Tangent

/-! ### The closed immersion criterion -/

section Criterion

/-- A morphism out of a Jacobson scheme which is unramified at every closed point of the source
is formally unramified. -/
theorem formallyUnramified_of_unramifiedAt_closedPoints {X Y : Scheme.{u}} [JacobsonSpace X]
    (f : X ⟶ Y) (h : ∀ x : X, IsClosed ({x} : Set X) → UnramifiedAt f x) :
    FormallyUnramified f := by
  have hopen : IsOpen {x : X | UnramifiedAt f x} := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨U, hU, hxU, V, hV, e, hu⟩ := hx
    exact Filter.mem_of_superset (U.isOpen.mem_nhds hxU)
      (fun y hy => ⟨U, hU, hy, V, hV, e, hu⟩)
  have hall (x : X) : UnramifiedAt f x := by
    by_contra hx
    obtain ⟨y, hy, hyclosed⟩ := nonempty_inter_closedPoints
      (Set.nonempty_of_mem hx) hopen.isClosed_compl.isLocallyClosed
    exact hy (h y hyclosed)
  rw [HasRingHomProperty.iff_exists_appLE (P := @FormallyUnramified)
    (RingHom.FormallyUnramified.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.FormallyUnramified.holdsForLocalizationAway).left]
  intro x
  obtain ⟨U, hU, hx, V, hV, e, hu⟩ := hall x
  let _ : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  have := hu
  exact ⟨⟨V, hV⟩, ⟨U, hU⟩, hx, e, Algebra.Unramified.formallyUnramified⟩

/-- Over an algebraically closed field, a proper formally unramified morphism of schemes which is
injective on `k`-points is a monomorphism. -/
theorem mono_of_isProper_of_formallyUnramified {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ Spec (.of k)) [IsProper f]
    [LocallyOfFiniteType (f ≫ q)] [FormallyUnramified f]
    (hinj : ∀ a b : Spec (.of k) ⟶ X, a ≫ (f ≫ q) = 𝟙 _ → b ≫ (f ≫ q) = 𝟙 _ →
      a ≫ f = b ≫ f → a = b) : Mono f := by
  set Z := Limits.pullback f f with hZ
  set r : Z ⟶ Spec (.of k) := Limits.pullback.fst f f ≫ (f ≫ q) with hr
  have : LocallyOfFiniteType r := by rw [hr]; infer_instance
  have : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace r
  set d := Limits.pullback.diagonal f with hd'
  have hd : IsClosed (Set.range d) := d.isClosedEmbedding.isClosed_range
  have hc : closedPoints Z ⊆ Set.range d := by
    intro z hz
    set c := pointOfClosedPoint r z hz with hcdef
    have ha : (c ≫ Limits.pullback.fst f f) ≫ (f ≫ q) = 𝟙 _ := by
      simpa [hr, Category.assoc] using pointOfClosedPoint_comp r z hz
    have hb : (c ≫ Limits.pullback.snd f f) ≫ (f ≫ q) = 𝟙 _ := by
      calc (c ≫ Limits.pullback.snd f f) ≫ (f ≫ q)
          = c ≫ (Limits.pullback.snd f f ≫ f) ≫ q := by simp only [Category.assoc]
        _ = c ≫ (Limits.pullback.fst f f ≫ f) ≫ q := by rw [Limits.pullback.condition]
        _ = (c ≫ Limits.pullback.fst f f) ≫ (f ≫ q) := by simp only [Category.assoc]
        _ = 𝟙 _ := ha
    have hab : c ≫ Limits.pullback.fst f f = c ≫ Limits.pullback.snd f f :=
      hinj _ _ ha hb (by simp only [Category.assoc, Limits.pullback.condition])
    have hcd : (c ≫ Limits.pullback.fst f f) ≫ d = c := by
      apply Limits.pullback.hom_ext
      · simp [hd']
      · simpa [hd'] using hab
    refine ⟨(c ≫ Limits.pullback.fst f f) (IsLocalRing.closedPoint k), ?_⟩
    change ((c ≫ Limits.pullback.fst f f) ≫ d) (IsLocalRing.closedPoint k) = z
    rw [hcd]
    exact pointOfClosedPoint_apply r z hz _
  have : Surjective d := ⟨fun z => by
    have hz : z ∈ closure (closedPoints Z) := by rw [closure_closedPoints]; trivial
    exact (closure_minimal hc hd) hz⟩
  have : IsIso d := (isIso_iff_isOpenImmersion_and_surjective d).mpr
    ⟨inferInstance, inferInstance⟩
  exact (Limits.pullback.isIso_diagonal_iff f).mp inferInstance

/-- Over an algebraically closed field, a proper formally unramified morphism of schemes which is
injective on `k`-points is a closed immersion. -/
theorem isClosedImmersion_of_isProper_of_formallyUnramified {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ Spec (.of k)) [IsProper f]
    [LocallyOfFiniteType (f ≫ q)] [FormallyUnramified f]
    (hinj : ∀ a b : Spec (.of k) ⟶ X, a ≫ (f ≫ q) = 𝟙 _ → b ≫ (f ≫ q) = 𝟙 _ →
      a ≫ f = b ≫ f → a = b) : IsClosedImmersion f :=
  have : Mono f := mono_of_isProper_of_formallyUnramified f q hinj
  (IsClosedImmersion.iff_isProper_and_mono f).mpr ⟨inferInstance, inferInstance⟩

/-- **The geometric half of Stacks Project, Tag 0E8S.** Let `f : X ⟶ Y` be a proper, formally
unramified morphism of schemes over an algebraically closed field `k`, with `X` locally of finite
type over `k`. Let `θ : f^* ℳ ≅ ℒ`, and let `ψ` be obtained from a family `t` of global sections
of `ℳ` by pulling back along `f` and transporting along `θ`. If `ψ` separates the closed points
of `X`, then `f` is a closed immersion.

Formal unramifiedness is a hypothesis here, not a consequence of separation of tangent vectors:
the implication from injectivity of the tangent maps is
[Stacks, Tag 0B2G](https://stacks.math.columbia.edu/tag/0B2G), which is not proved in this
repository. See the section "What is not proved here" of this module. -/
theorem isClosedImmersion_of_separatesClosedPoints {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ Spec (.of k)) [IsProper f]
    [LocallyOfFiniteType (f ≫ q)] [FormallyUnramified f]
    {M : Y.Modules} {L : X.Modules} (θ : (Scheme.Modules.pullback f).obj M ≅ L)
    {V : Type v} {t : V → M.val.obj (op ⊤)} {ψ : V → L.val.obj (op ⊤)}
    (htψ : ∀ v, θ.hom.val.app (op ⊤) (pullbackSectionTop f M (t v)) = ψ v)
    (hsep : SeparatesClosedPoints ψ) : IsClosedImmersion f :=
  isClosedImmersion_of_isProper_of_formallyUnramified f q
    (injective_of_separatesClosedPoints f (f ≫ q) θ htψ hsep)

end Criterion

end AlgebraicGeometry

end
