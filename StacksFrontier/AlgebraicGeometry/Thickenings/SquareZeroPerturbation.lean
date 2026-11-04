module

public import StacksFrontier.AlgebraicGeometry.Thickenings.FirstOrderConormalInclusion

/-!
# Perturbing a morphism of schemes by a square-zero derivation

Let `f : X ⟶ Y` be a morphism of schemes. A **square-zero perturbation** of `f` is a rule
assigning to every open `V` of `Y` an additive map `Γ(Y, V) ⟶ Γ(X, f⁻¹V)` which is a derivation
along `f^♯`, is natural in `V`, and whose values multiply to zero. The data is exactly what is
needed for `s ↦ f^♯ s + D s` to be a second ring map `Γ(Y, V) ⟶ Γ(X, f⁻¹V)`: the cross term in
the product vanishes and the two surviving terms are the two halves of the Leibniz rule.

Being natural in `V`, the perturbed comorphism is a morphism of presheaves of rings, so
`(f.base, f^♯ + D)` is a morphism of presheafed spaces. It is a morphism of **locally** ringed
spaces as well, hence a morphism of schemes: on stalks it differs from `f` by a nilpotent, and a
ring map between local rings that differs from a local one by a nilpotent is local.

## Main definitions

* `Stacks.Thickenings.SquareZeroPerturbation`: the data above.
* `Stacks.Thickenings.SquareZeroPerturbation.perturb`: the morphism of schemes `X ⟶ Y` with the
  same underlying map as `f` and comorphism `f^♯ + D`.

## Main results

* `Stacks.Thickenings.presheaf_map_eq`: restriction maps of a structure sheaf do not depend on the
  chosen morphism of opens, the category of opens being thin.
* `Stacks.Thickenings.SquareZeroPerturbation.perturb_base`: the perturbed morphism has the same
  underlying continuous map as `f`.
* `Stacks.Thickenings.SquareZeroPerturbation.perturb_app`: its comorphism is `f^♯ + D`.
* `Stacks.Thickenings.SquareZeroPerturbation.isLocalHom_stalkMap`: the perturbed morphism of
  presheafed spaces induces local ring homomorphisms on stalks.

## Implementation notes

The naturality field is stated for an inclusion `W ≤ V` of opens rather than for an arbitrary
morphism of `(Y.Opens)ᵒᵖ`, which is the form a user can supply; the two agree because the
category of opens is thin, so the morphism occurring in a given restriction map may be replaced
by `CategoryTheory.homOfLE` of its `≤` (`Stacks.Thickenings.presheaf_map_eq`).

Localness on stalks is the only step that is not formal. A germ of `𝒪_Y` at `f x` is represented
by a section `s` over some open `V`, and the difference of the two stalk maps on that germ is the
germ of `D s`, which squares to zero by the `value_mul_value` field. So the two stalk maps differ
by a nilpotent element of the local ring `𝒪_{X,x}`; a nilpotent lies in the maximal ideal, so
adding one neither creates nor destroys a unit, and the perturbed map inherits `IsLocalHom` from
`f`.

The fields of `Stacks.Thickenings.SquareZeroPerturbation` are named `value_zero`, `value_one`, …
rather than `map_zero`, `map_one`, … so that inside the namespace they do not shadow the
root-level lemmas of those names, which the proofs of the ring-homomorphism laws use on `f^♯`.

## References

* [Stacks Project, Tag 02H5](https://stacks.math.columbia.edu/tag/02H5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.Thickenings

/-- Restriction maps of the structure sheaf between two opens do not depend on the chosen
inclusion: the category of opens is thin. -/
theorem presheaf_map_eq {X : Scheme.{u}} {A B : (X.Opens)ᵒᵖ} (u v : A ⟶ B) :
    X.presheaf.map u = X.presheaf.map v := by
  rw [show u = v from Quiver.Hom.unop_inj (Subsingleton.elim _ _)]

/-- A restriction map of the structure sheaf from an open to itself is the identity: the only
morphism of opens available is the identity. -/
theorem presheaf_map_self {X : Scheme.{u}} {A : (X.Opens)ᵒᵖ} (u : A ⟶ A)
    (x : X.presheaf.obj A) : (X.presheaf.map u).hom x = x := by
  rw [presheaf_map_eq u (𝟙 A), CategoryTheory.Functor.map_id]
  rfl

/-- **Two composed restriction maps of a sheaf of modules on a scheme are a single one.** The
category of opens is thin, so the composite of the two given morphisms of opens is the third one,
whatever it is. -/
theorem module_map_map {X : Scheme.{u}}
    {M : SheafOfModules.{u} (structureSheafRing X.toLocallyRingedSpace.toRingedSpace)}
    {A B C : (X.Opens)ᵒᵖ} (u : A ⟶ B) (v : B ⟶ C) (w : A ⟶ C) (m : M.val.obj A) :
    M.val.map v (M.val.map u m) = M.val.map w m := by
  obtain rfl : w = u ≫ v := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  exact (PresheafOfModules.map_comp_apply M.val u v m).symm

variable {X Y : Scheme.{u}}

/-- **A square-zero perturbation of a morphism of schemes `f : X ⟶ Y`.** For every open `V` of
`Y` an additive map `Γ(Y, V) ⟶ Γ(X, f⁻¹V)` satisfying the Leibniz rule along `f^♯`, natural in
`V`, and with the property that any two values multiply to zero.

The point of the data is `Stacks.Thickenings.SquareZeroPerturbation.perturb`: `f^♯ + D` is again
the comorphism of a morphism of schemes `X ⟶ Y`. -/
structure SquareZeroPerturbation (f : X ⟶ Y) where
  /-- The value of the perturbation on a section over an open of `Y`. -/
  value : ∀ V : Y.Opens, Γ(Y, V) → Γ(X, f ⁻¹ᵁ V)
  /-- The perturbation kills `0`. -/
  value_zero : ∀ V : Y.Opens, value V 0 = 0
  /-- The perturbation kills `1`, as a derivation must. -/
  value_one : ∀ V : Y.Opens, value V 1 = 0
  /-- The perturbation is additive. -/
  value_add : ∀ (V : Y.Opens) (s t : Γ(Y, V)), value V (s + t) = value V s + value V t
  /-- The Leibniz rule along the comorphism of `f`. -/
  value_leibniz : ∀ (V : Y.Opens) (s t : Γ(Y, V)),
    value V (s * t) = (f.app V).hom s * value V t + (f.app V).hom t * value V s
  /-- Any two values of the perturbation multiply to zero. -/
  value_mul_value : ∀ (V : Y.Opens) (s t : Γ(Y, V)), value V s * value V t = 0
  /-- The perturbation commutes with restriction to a smaller open. -/
  value_naturality : ∀ {V W : Y.Opens} (hWV : W ≤ V) (s : Γ(Y, V)),
    value W ((Y.presheaf.map (homOfLE hWV).op).hom s) =
      (X.presheaf.map (homOfLE (f.preimage_mono hWV)).op).hom (value V s)

namespace SquareZeroPerturbation

variable {f : X ⟶ Y} (D : SquareZeroPerturbation f)

/-- The perturbation commutes with restriction along an arbitrary morphism of opens, not only
along a `CategoryTheory.homOfLE`: the category of opens is thin. -/
theorem value_naturality' {V W : (Y.Opens)ᵒᵖ} (r : V ⟶ W) (s : Γ(Y, V.unop)) :
    D.value W.unop ((Y.presheaf.map r).hom s) =
      (X.presheaf.map ((Opens.map f.base).map r.unop).op).hom (D.value V.unop s) := by
  rw [presheaf_map_eq r (homOfLE r.unop.le).op,
    presheaf_map_eq ((Opens.map f.base).map r.unop).op (homOfLE (f.preimage_mono r.unop.le)).op]
  exact D.value_naturality r.unop.le s

/-- **The perturbed comorphism** `f^♯ + D`, as a morphism of presheaves of commutative rings
`𝒪_Y ⟶ f_* 𝒪_X`. Each component is a ring homomorphism: the cross term of a product is zero by
`Stacks.Thickenings.SquareZeroPerturbation.value_mul_value` and the two remaining terms are the
Leibniz rule. -/
def comorphism : Y.presheaf ⟶ f.base _* X.presheaf where
  app V := CommRingCat.ofHom
    { toFun := fun s ↦ (f.app V.unop).hom s + D.value V.unop s
      map_one' := by
        change (f.app V.unop).hom 1 + D.value V.unop 1 = 1
        rw [D.value_one, add_zero, _root_.map_one]
      map_zero' := by
        change (f.app V.unop).hom 0 + D.value V.unop 0 = 0
        rw [D.value_zero, add_zero, _root_.map_zero]
      map_add' := fun s t ↦ by
        change (f.app V.unop).hom (s + t) + D.value V.unop (s + t) = _
        rw [D.value_add, _root_.map_add]
        ring
      map_mul' := fun s t ↦ by
        change (f.app V.unop).hom (s * t) + D.value V.unop (s * t) = _
        rw [D.value_leibniz, _root_.map_mul]
        have hz := D.value_mul_value V.unop s t
        linear_combination (norm := ring_nf) -hz }
  naturality := by
    intro V W r
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro s
    have hf : (f.app W.unop).hom ((Y.presheaf.map r).hom s) =
        (X.presheaf.map ((Opens.map f.base).map r.unop).op).hom ((f.app V.unop).hom s) := by
      rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
    change (f.app W.unop).hom ((Y.presheaf.map r).hom s) +
        D.value W.unop ((Y.presheaf.map r).hom s) =
      (X.presheaf.map ((Opens.map f.base).map r.unop).op).hom
        ((f.app V.unop).hom s + D.value V.unop s)
    rw [hf, D.value_naturality' r s]
    exact (_root_.map_add _ _ _).symm

/-- **The perturbed morphism of presheafed spaces**: the underlying map of `f` together with the
comorphism `f^♯ + D`. -/
def perturbPsh : X.toPresheafedSpace ⟶ Y.toPresheafedSpace where
  base := f.base
  c := D.comorphism

/-- The comorphism of `Stacks.Thickenings.SquareZeroPerturbation.perturbPsh` on a section. -/
theorem perturbPsh_c_app (V : Y.Opens) (s : Γ(Y, V)) :
    ((perturbPsh D).c.app (op V)).hom s = (f.app V).hom s + D.value V s := rfl

/-- **A ring map differing from a local one by nilpotents is local.** If `φ a - ψ a` is nilpotent
for every `a` and `φ` reflects units, then so does `ψ`: a nilpotent added to a unit is a unit, and
`ψ a + (φ a - ψ a) = φ a`. -/
theorem isLocalHom_of_isNilpotent_sub {A B : Type u} [CommRing A] [CommRing B] (φ ψ : A →+* B)
    (hnil : ∀ a, IsNilpotent (φ a - ψ a)) (h : IsLocalHom φ) : IsLocalHom ψ :=
  ⟨fun a ha ↦ h.1 a (by
    have hu := (hnil a).isUnit_add_right_of_commute ha (Commute.all _ _)
    convert hu using 1
    abel)⟩

/-- **The perturbed morphism of presheafed spaces is local on stalks.** On a germ represented by
a section `s` over `V`, the two stalk maps differ by the germ of `D s`, which squares to zero; a
nilpotent lies in the maximal ideal of a local ring, so adding one preserves and reflects
units. -/
theorem isLocalHom_stalkMap (x : X) :
    IsLocalHom ((PresheafedSpace.Hom.stalkMap (perturbPsh D) x)).hom := by
  have hloc : IsLocalHom (LocallyRingedSpace.Hom.stalkMap f.toLRSHom x).hom :=
    LocallyRingedSpace.isLocalHomStalkMap f.toLRSHom x
  have horig : ∀ (V : Y.Opens) (hx : f.base x ∈ V) (s : Γ(Y, V)),
      (LocallyRingedSpace.Hom.stalkMap f.toLRSHom x).hom
          ((Y.presheaf.germ V (f.base x) hx).hom s) =
        (X.presheaf.germ (f ⁻¹ᵁ V) x hx).hom ((f.app V).hom s) :=
    fun V hx s ↦ LocallyRingedSpace.stalkMap_germ_apply f.toLRSHom V x hx s
  have hpert : ∀ (V : Y.Opens) (hx : f.base x ∈ V) (s : Γ(Y, V)),
      (PresheafedSpace.Hom.stalkMap (perturbPsh D) x).hom
          ((Y.presheaf.germ V (f.base x) hx).hom s) =
        (X.presheaf.germ (f ⁻¹ᵁ V) x hx).hom ((f.app V).hom s + D.value V s) :=
    fun V hx s ↦ PresheafedSpace.stalkMap_germ_apply (perturbPsh D) V x hx s
  refine isLocalHom_of_isNilpotent_sub (LocallyRingedSpace.Hom.stalkMap f.toLRSHom x).hom
    (PresheafedSpace.Hom.stalkMap (perturbPsh D) x).hom (fun z ↦ ?_) hloc
  obtain ⟨V, hx, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq Y.presheaf z
  have hd : (LocallyRingedSpace.Hom.stalkMap f.toLRSHom x).hom
          ((Y.presheaf.germ V (f.base x) hx).hom s) -
        (PresheafedSpace.Hom.stalkMap (perturbPsh D) x).hom
          ((Y.presheaf.germ V (f.base x) hx).hom s) =
      -(X.presheaf.germ (f ⁻¹ᵁ V) x hx).hom (D.value V s) := by
    rw [horig V hx s, hpert V hx s, ← map_sub,
      show (f.app V).hom s - ((f.app V).hom s + D.value V s) = -D.value V s by ring, map_neg]
  have hsq : D.value V s ^ 2 = 0 := by
    rw [pow_two]; exact D.value_mul_value V s s
  have hnil : IsNilpotent (-(X.presheaf.germ (f ⁻¹ᵁ V) x hx).hom (D.value V s)) := by
    refine ⟨2, ?_⟩
    rw [neg_pow, ← map_pow, hsq, map_zero, mul_zero]
  exact (congrArg IsNilpotent hd).mpr hnil

/-- **The morphism of schemes obtained by perturbing `f` by `D`.** Its underlying map is that of
`f` and its comorphism is `f^♯ + D`; it is a morphism of locally ringed spaces by
`Stacks.Thickenings.SquareZeroPerturbation.isLocalHom_stalkMap`.

For a first-order thickening `i : T ⟶ T'` and a derivation taking values in the defining ideal of
`i` this is the lift `θ ⬝ a'` of [Stacks Project, Tag 0CK1]. -/
def perturb : X ⟶ Y :=
  ⟨LocallyRingedSpace.homMk (InducedCategory.homMk (perturbPsh D)) (isLocalHom_stalkMap D)⟩

/-- The perturbed morphism has the same underlying continuous map as `f`. -/
@[simp]
theorem perturb_base : (perturb D).base = f.base := rfl

/-- The perturbed morphism has the same preimages of opens as `f`. -/
theorem perturb_preimage (V : Y.Opens) : (perturb D) ⁻¹ᵁ V = f ⁻¹ᵁ V := rfl

/-- **The comorphism of the perturbed morphism is `f^♯ + D`.** -/
theorem perturb_app (V : Y.Opens) (s : Γ(Y, V)) :
    ((perturb D).app V).hom s =
      @HAdd.hAdd Γ(X, f ⁻¹ᵁ V) Γ(X, f ⁻¹ᵁ V) Γ(X, f ⁻¹ᵁ V) inferInstance
        ((f.app V).hom s) (D.value V s) :=
  perturbPsh_c_app D V s

end SquareZeroPerturbation

end Stacks.Thickenings

end
