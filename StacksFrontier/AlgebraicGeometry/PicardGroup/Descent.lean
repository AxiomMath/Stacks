module

public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Scheme
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialization.Basic

/-!
# Descending triviality of the Picard group along an open cover

Let `X` be a scheme. This file assembles the sheaf-theoretic half of
[Stacks, Tag 0BDA](https://stacks.math.columbia.edu/tag/0BDA): the three ways in which
triviality of `Pic` descends, namely along an isomorphism of schemes, along a two-open cover
whose units split, and along a single open over which regular functions extend.

Everything is phrased through *trivializing sections*. A section `a` of `L` over an open `T` is
said to trivialize `L` there when `c ↦ c ⬝ a|_V` is a bijection `𝒪_X(V) → L(V)` for every open
`V ≤ T`. This is the shape in which the two halves of [Stacks, Tag 0B8M] already speak
(`Stacks.SheafOfModules.isoUnitOver` builds a trivialization from such a section, and
`Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible` produces one locally), and the
whole gluing argument can be run in it: multiplying a trivializing section by a unit again
trivializes, two trivializing sections over one open differ by a unit, and a trivializing
section may be produced from, or turned into, an isomorphism `L ≅ 𝒪`.

## Main results

Over a ringed space, for a sheaf of modules `L`:

* `Stacks.SheafOfModules.exists_bijective_smul_of_iso_unit` and
  `Stacks.SheafOfModules.nonempty_iso_unit_of_bijective_smul_on_cover`: a trivialization of `L`
  is the same thing as a global section of `L` by which multiplication is bijective; for the
  second direction bijectivity on the opens below the members of an open cover suffices.
* `Stacks.SheafOfModules.exists_bijective_smul_of_over_iso_unit`: the converse of
  `Stacks.SheafOfModules.isoUnitOver` — a trivialization of `L` over the localized site on `T`
  produces a section of `L` over `T` trivializing it there.
* `Stacks.SheafOfModules.exists_units_smul_eq` and
  `Stacks.SheafOfModules.bijective_smul_units_smul`: two trivializing sections over one open
  differ by a unit, and scaling a trivializing section by a unit keeps it trivializing.
* `Stacks.SheafOfModules.nonempty_iso_unit_of_two_opens`: **the two-open gluing.** If `L` is
  trivialized over each of two opens covering the space and every unit on their intersection
  is a product of units from the two sides, then `L` is trivial.
* `Stacks.SheafOfModules.bijective_map_of_bijective_smul`: on opens where `L` is trivialized,
  the restriction maps of `L` are those of `𝒪_X`.

For a scheme `Y`:

* `Stacks.PicardGroup.subsingleton_of_iso`: `Pic` is trivial for one of two isomorphic schemes
  exactly when it is for the other.
* `Stacks.PicardGroup.subsingleton_of_isEmpty`: `Pic` of the empty scheme is trivial.
* `Stacks.PicardGroup.subsingleton_of_two_opens`: triviality of `Pic` from a two-open cover by
  opens with trivial Picard group whose units split on the intersection.
* `Stacks.PicardGroup.subsingleton_of_functions`: triviality of `Pic` descends from an open `W`
  with `Pic(W)` trivial, provided every regular function on `V ∩ W` extends uniquely to `V`,
  for every open `V`.

## Implementation notes

**Which `IsInvertible`.** `Stacks.SheafOfModules.IsInvertible` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorInvertible.lean`, the class the Picard group
of `StacksFrontier/AlgebraicGeometry/PicardGroup/Basic.lean` is built over and the one both
halves of Tag 0B8M speak. The repository also carries the definitionally identical
`AlgebraicGeometry.SheafOfModules.IsInvertible`; nothing here crosses between them.

**Which sheaf of rings.** The ringed-space results are stated over
`structureSheafRing X`, which is `@[reducible]`,
  rather than over
`AlgebraicGeometry.Scheme.ringCatSheaf`. This is not cosmetic: the module structure on
`L.val.obj (op V)` over the sections `Γ(X, V)` of the structure sheaf is found by instance
search through the former and **not** through the latter, so the scalar multiplications that
every statement here is about do not even elaborate in the `ringCatSheaf` spelling. Scheme-level
statements take `L : Y.Modules` and are read at `structureSheafRing Y.toRingedSpace`, which
elaboration accepts.

**The two spellings of a trivialization over an open.** `L.over T ≅ 𝒪|_T` on the localized site
`Over T` and `L.restrict T.ι ≅ 𝒪_T` on the open subscheme are converted into one another by
`Stacks.Modules.overIsoUnitOfRestrictIsoUnit` and
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.restrictIsoUnitOfOverIsoUnit`; neither is
re-derived.

## References

* [Stacks Project, Tag 0BDA](https://stacks.math.columbia.edu/tag/0BDA)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe v u w

namespace Stacks.SheafOfModules

/-! ### Trivializing sections -/

section Site

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- A component of an isomorphism of sheaves of modules is an isomorphism. -/
theorem isIso_val_app_of_iso {L M : SheafOfModules.{w} R} (e : L ≅ M) (A : Cᵒᵖ) :
    IsIso (e.hom.val.app A) :=
  ((PresheafOfModules.evaluation R.obj A).mapIso ((SheafOfModules.forget _).mapIso e)).isIso_hom

/-- Multiplication by a global section `s` is bijective on the sections over `A` exactly when
the component at `A` of the morphism `𝒪 ⟶ L` it determines is. -/
theorem bijective_unitHomEquiv_symm_val_app_iff (L : SheafOfModules.{w} R) (s : L.val.sections)
    (A : Cᵒᵖ) :
    Function.Bijective ((L.unitHomEquiv.symm s).val.app A).hom ↔
      Function.Bijective fun c : R.obj.obj A => c • s.eval A := Iff.rfl

/-- **A trivialization of `L` is multiplication by a global section**: if `L ≅ 𝒪` then there is
a global section of `L` by which multiplication is bijective on the sections over every object
of the site. -/
theorem exists_bijective_smul_of_iso_unit (L : SheafOfModules.{w} R)
    (e : L ≅ SheafOfModules.unit R) :
    ∃ s : L.val.sections, ∀ A : Cᵒᵖ, Function.Bijective fun c : R.obj.obj A => c • s.eval A := by
  refine ⟨L.unitHomEquiv e.inv, fun A => ?_⟩
  have hs : L.unitHomEquiv.symm (L.unitHomEquiv e.inv) = e.inv :=
    L.unitHomEquiv.symm_apply_apply _
  have h : IsIso ((L.unitHomEquiv.symm (L.unitHomEquiv e.inv)).val.app A) := by
    rw [hs]; exact isIso_val_app_of_iso e.symm A
  exact (bijective_unitHomEquiv_symm_val_app_iff L _ A).1
    ((ConcreteCategory.isIso_iff_bijective _).mp h)

end Site

/-- The unit twist behind the two-open gluing, at abstract types: if `q` and `r` are inverse and
`p ⬝ r = t`, then multiplication by `p` agrees with multiplication by `q` after `t`. -/
private theorem smul_eq_smul_smul_of_mul_eq {A : Type*} [CommRing A] {M : Type*}
    [AddCommGroup M] [Module A M] {p q r t : A} (hqr : q * r = 1) (hprt : p * r = t) (m : M) :
    p • m = q • (t • m) := by
  have h : q * t = p := by
    rw [← hprt]
    calc q * (p * r) = q * r * p := by ring
      _ = p := by rw [hqr, one_mul]
  rw [← mul_smul, h]

section RingedSpace

variable {X : RingedSpace.{u, u}} (L : SheafOfModules.{u} (structureSheafRing X))

/-- A morphism of sheaves of modules that is bijective on the sections over every open contained
in a member of an open cover is bijective on the sections over every open. -/
theorem bijective_app_of_bijective_on_cover
    {M N : SheafOfModules.{u} (structureSheafRing X)} (φ : M ⟶ N)
    {ι : Type*} (W : ι → Opens X.carrier) (hW : IsOpenCover W)
    (hφ : ∀ (i : ι) (V : Opens X.carrier), V ≤ W i → Function.Bijective (φ.val.app (op V)).hom)
    (V : Opens X.carrier) : Function.Bijective (φ.val.app (op V)).hom := by
  have hB : Opens.IsBasis
      (Set.range (Subtype.val : {V : Opens X.carrier | ∃ i, V ≤ W i} → Opens X.carrier)) := by
    rw [Subtype.range_coe_subtype]
    refine Opens.isBasis_iff_nbhd.mpr fun {V x} hx => ?_
    obtain ⟨i, hi⟩ := hW.exists_mem x
    exact ⟨V ⊓ W i, ⟨i, inf_le_right⟩, ⟨hx, hi⟩, inf_le_left⟩
  let F : TopCat.Sheaf AddCommGrpCat X.carrier := ⟨M.val.presheaf, SheafOfModules.isSheaf M⟩
  let G : TopCat.Sheaf AddCommGrpCat X.carrier := ⟨N.val.presheaf, SheafOfModules.isSheaf N⟩
  let ψ : F ⟶ G := ⟨(PresheafOfModules.toPresheaf _).map φ.val⟩
  have : IsIso ψ := TopCat.Sheaf.isIso_iff_isIso_basis hB
    (fun ⟨V, i, hi⟩ => (ConcreteCategory.isIso_iff_bijective _).mpr (hφ i V hi))
  exact (ConcreteCategory.isIso_iff_bijective
    (((TopCat.Sheaf.forget AddCommGrpCat X.carrier).map ψ).app (op V))).mp inferInstance

/-- **A global section by which multiplication is bijective on an open cover trivializes `L`.**
Bijectivity on all of the opens below a member of the cover is enough, by the sheaf condition. -/
theorem nonempty_iso_unit_of_bijective_smul_on_cover {ι : Type*} (s : L.val.sections)
    (W : ι → Opens X.carrier) (hW : IsOpenCover W)
    (hs : ∀ (i : ι) (V : Opens X.carrier), V ≤ W i →
      Function.Bijective fun c : X.presheaf.obj (op V) => c • s.eval (op V)) :
    Nonempty (L ≅ SheafOfModules.unit (structureSheafRing X)) := by
  have h : IsIso (L.unitHomEquiv.symm s) := by
    refine isIso_of_isIso_val_app _ fun A => ?_
    refine (ConcreteCategory.isIso_iff_bijective _).mpr ?_
    exact bijective_app_of_bijective_on_cover (L.unitHomEquiv.symm s) W hW
      (fun i V hV => (bijective_unitHomEquiv_symm_val_app_iff L s (op V)).2 (hs i V hV)) A.unop
  exact ⟨(@asIso _ _ _ _ (L.unitHomEquiv.symm s) h).symm⟩

/-- **The converse of `isoUnitOver`.** A trivialization of `L` over the localized site on `T`
gives a section of `L` over `T` by which multiplication is bijective on every smaller open. -/
theorem exists_bijective_smul_of_over_iso_unit (T : Opens X.carrier)
    (e : L.over T ≅ SheafOfModules.unit ((structureSheafRing X).over T)) :
    ∃ a : L.val.obj (op T), ∀ (V : Opens X.carrier) (hV : V ≤ T),
      Function.Bijective fun c : X.presheaf.obj (op V) => c • (L.val.map (homOfLE hV).op a) := by
  obtain ⟨s, hs⟩ := exists_bijective_smul_of_iso_unit _ e
  refine ⟨s.eval (op (Over.mk (homOfLE (le_refl T)))), fun V hV => ?_⟩
  have hres : L.val.map (homOfLE hV).op (s.eval (op (Over.mk (homOfLE (le_refl T)))))
      = s.eval (op (Over.mk (homOfLE hV))) :=
    PresheafOfModules.sections_property s
      (Over.homMk (homOfLE hV) : Over.mk (homOfLE hV) ⟶ Over.mk (homOfLE (le_refl T))).op
  rw [hres]
  exact hs (op (Over.mk (homOfLE hV)))

/-- The restriction of a scalar multiple, with the scalar written as a section of the structure
sheaf rather than of its `RingCat`-valued companion. -/
theorem map_smul_restrict {V W : Opens X.carrier} (h : V ≤ W) (c : X.presheaf.obj (op W))
    (x : L.val.obj (op W)) :
    L.val.map (homOfLE h).op (c • x)
      = (X.presheaf.map (homOfLE h).op c) • L.val.map (homOfLE h).op x :=
  L.val.map_smul _ _ _

/-- Restriction in two steps. -/
theorem map_restrict_comp {P Q R : Opens X.carrier} (hQP : Q ≤ P) (hPR : P ≤ R)
    (a : L.val.obj (op R)) :
    L.val.map (homOfLE hQP).op (L.val.map (homOfLE hPR).op a)
      = L.val.map (homOfLE (hQP.trans hPR)).op a := by
  rw [← L.val.map_comp_apply]
  exact L.val.congr_map_apply (Subsingleton.elim _ _) a

/-- Two sections trivializing `L` over the same open differ by a unit. -/
theorem exists_units_smul_eq (V : Opens X.carrier) (a b : L.val.obj (op V))
    (ha : Function.Bijective fun c : X.presheaf.obj (op V) => c • a)
    (hb : Function.Bijective fun c : X.presheaf.obj (op V) => c • b) :
    ∃ u : (X.presheaf.obj (op V))ˣ, (u : X.presheaf.obj (op V)) • a = b := by
  obtain ⟨c, hc⟩ := ha.2 b
  obtain ⟨d, hd⟩ := hb.2 a
  simp only at hc hd
  have h1 : d * c = 1 := ha.1 (show (d * c) • a = (1 : X.presheaf.obj (op V)) • a by
    rw [mul_smul, hc, hd, one_smul])
  exact ⟨⟨c, d, by rw [mul_comm]; exact h1, h1⟩, hc⟩

/-- Scaling a trivializing section by a unit keeps it trivializing. -/
theorem bijective_smul_units_smul (V : Opens X.carrier) (a : L.val.obj (op V))
    (ha : ∀ (V' : Opens X.carrier) (hV' : V' ≤ V),
      Function.Bijective fun c : X.presheaf.obj (op V') => c • (L.val.map (homOfLE hV').op a))
    (u : (X.presheaf.obj (op V))ˣ) (V' : Opens X.carrier) (hV' : V' ≤ V) :
    Function.Bijective fun c : X.presheaf.obj (op V') =>
      c • (L.val.map (homOfLE hV').op ((u : X.presheaf.obj (op V)) • a)) := by
  have hmap : L.val.map (homOfLE hV').op ((u : X.presheaf.obj (op V)) • a)
      = (X.presheaf.map (homOfLE hV').op (u : X.presheaf.obj (op V)))
        • L.val.map (homOfLE hV').op a := L.val.map_smul _ _ _
  have hu : IsUnit (X.presheaf.map (homOfLE hV').op (u : X.presheaf.obj (op V))) :=
    u.isUnit.map (X.presheaf.map (homOfLE hV').op).hom
  rw [hmap]
  have hcomp : (fun c : X.presheaf.obj (op V') =>
      c • ((X.presheaf.map (homOfLE hV').op (u : X.presheaf.obj (op V)))
        • L.val.map (homOfLE hV').op a))
      = (fun c : X.presheaf.obj (op V') => c • L.val.map (homOfLE hV').op a) ∘
        (fun c : X.presheaf.obj (op V') =>
          c * X.presheaf.map (homOfLE hV').op (u : X.presheaf.obj (op V))) := by
    funext c; exact (mul_smul _ _ _).symm
  rw [hcomp]
  exact (ha V' hV').comp (IsUnit.isUnit_iff_mulRight_bijective.mp hu)

/-- A global section of `L` from its restrictions to a two-open cover. -/
theorem exists_sections_eval_eq (V W : Opens X.carrier) (hcover : V ⊔ W = ⊤)
    (a : L.val.obj (op V)) (b : L.val.obj (op W))
    (hab : L.val.map (homOfLE (inf_le_left : V ⊓ W ≤ V)).op a =
      L.val.map (homOfLE (inf_le_right : V ⊓ W ≤ W)).op b) :
    ∃ s : L.val.sections, s.eval (op V) = a ∧ s.eval (op W) = b := by
  classical
  let F : TopCat.Sheaf AddCommGrpCat X.carrier := ⟨L.val.presheaf, SheafOfModules.isSheaf L⟩
  let C : Bool → Opens X.carrier := fun i => if i then V else W
  let d : ∀ i, L.val.presheaf.obj (op (C i)) :=
    fun i => if h : i then h ▸ a else (Bool.eq_false_iff.mpr h) ▸ b
  have key : ∀ (T : Opens X.carrier) (hTV : T ≤ V) (hTW : T ≤ W),
      L.val.map (homOfLE hTV).op a = L.val.map (homOfLE hTW).op b := by
    intro T hTV hTW
    have h1 : L.val.map (homOfLE hTV).op a
        = L.val.map ((homOfLE (inf_le_left : V ⊓ W ≤ V)).op ≫
            (homOfLE (le_inf hTV hTW)).op) a :=
      L.val.congr_map_apply (Subsingleton.elim _ _) a
    have h2 : L.val.map (homOfLE hTW).op b
        = L.val.map ((homOfLE (inf_le_right : V ⊓ W ≤ W)).op ≫
            (homOfLE (le_inf hTV hTW)).op) b :=
      L.val.congr_map_apply (Subsingleton.elim _ _) b
    rw [h1, h2, L.val.map_comp_apply, L.val.map_comp_apply, hab]
  have hc : TopCat.Presheaf.IsCompatible L.val.presheaf C d := by
    intro i j
    cases i <;> cases j
    · rfl
    · exact (key (C false ⊓ C true) inf_le_right inf_le_left).symm
    · exact key (C true ⊓ C false) inf_le_left inf_le_right
    · rfl
  obtain ⟨g₀, hg, -⟩ := F.existsUnique_gluing' C ⊤ (fun _ => homOfLE le_top)
    (by simp [C, iSup_bool_eq, hcover]) d hc
  let g : L.val.obj (op ⊤) := g₀
  have hg' : ∀ i, L.val.map (homOfLE (le_top (a := C i))).op g = d i := hg
  refine ⟨PresheafOfModules.sectionsMk
    (fun A => L.val.map (homOfLE (le_top (a := A.unop))).op g) ?_, hg' true, hg' false⟩
  intro A B f
  rw [← L.val.map_comp_apply]
  exact L.val.congr_map_apply (Subsingleton.elim _ _) g

/-- **Two trivializing sections on a two-open cover glue after a unit twist.** If `L` is
trivialized by `a` over `V` and by `b` over `W`, where `V ∪ W` is everything, and if every unit
on `V ∩ W` is a product of the restrictions of a unit on `V` and a unit on `W`, then `L` is
trivial.

This is the sheaf-theoretic half of [Stacks, Tag 0BDA]: the twisted sections `u ⬝ a` and
`v⁻¹ ⬝ b` agree on `V ∩ W`, hence glue to a global section of `L`, which still trivializes `L`
over each of `V` and `W` because it differs from `a` resp. `b` by a unit. -/
theorem nonempty_iso_unit_of_two_opens (V W : Opens X.carrier) (hcover : V ⊔ W = ⊤)
    (a : L.val.obj (op V))
    (ha : ∀ (V' : Opens X.carrier) (hV' : V' ≤ V),
      Function.Bijective fun c : X.presheaf.obj (op V') => c • (L.val.map (homOfLE hV').op a))
    (b : L.val.obj (op W))
    (hb : ∀ (W' : Opens X.carrier) (hW' : W' ≤ W),
      Function.Bijective fun c : X.presheaf.obj (op W') => c • (L.val.map (homOfLE hW').op b))
    (hsplit : ∀ w : (X.presheaf.obj (op (V ⊓ W)))ˣ,
      ∃ (u : (X.presheaf.obj (op V))ˣ) (v : (X.presheaf.obj (op W))ˣ),
        X.presheaf.map (homOfLE (inf_le_left : V ⊓ W ≤ V)).op (u : X.presheaf.obj (op V)) *
            X.presheaf.map (homOfLE (inf_le_right : V ⊓ W ≤ W)).op (v : X.presheaf.obj (op W))
          = (w : X.presheaf.obj (op (V ⊓ W)))) :
    Nonempty (L ≅ SheafOfModules.unit (structureSheafRing X)) := by
  classical
  obtain ⟨w, hw⟩ := exists_units_smul_eq L (V ⊓ W)
    (L.val.map (homOfLE (inf_le_left : V ⊓ W ≤ V)).op a)
    (L.val.map (homOfLE (inf_le_right : V ⊓ W ≤ W)).op b) (ha _ inf_le_left) (hb _ inf_le_right)
  obtain ⟨u, v, huv⟩ := hsplit w
  have hvinv : X.presheaf.map (homOfLE (inf_le_right : V ⊓ W ≤ W)).op
        ((v⁻¹ : (X.presheaf.obj (op W))ˣ) : X.presheaf.obj (op W)) *
      X.presheaf.map (homOfLE (inf_le_right : V ⊓ W ≤ W)).op (v : X.presheaf.obj (op W)) = 1 := by
    rw [← map_mul, show ((v⁻¹ : (X.presheaf.obj (op W))ˣ) : X.presheaf.obj (op W)) *
      (v : X.presheaf.obj (op W)) = 1 from v.inv_mul]
    exact map_one (X.presheaf.map (homOfLE (inf_le_right : V ⊓ W ≤ W)).op).hom
  have hab : L.val.map (homOfLE (inf_le_left : V ⊓ W ≤ V)).op
        ((u : X.presheaf.obj (op V)) • a) =
      L.val.map (homOfLE (inf_le_right : V ⊓ W ≤ W)).op
        (((v⁻¹ : (X.presheaf.obj (op W))ˣ) : X.presheaf.obj (op W)) • b) := by
    rw [map_smul_restrict L (inf_le_left : V ⊓ W ≤ V) (u : X.presheaf.obj (op V)) a,
      map_smul_restrict L (inf_le_right : V ⊓ W ≤ W)
        ((v⁻¹ : (X.presheaf.obj (op W))ˣ) : X.presheaf.obj (op W)) b,
      ← hw]
    exact smul_eq_smul_smul_of_mul_eq (M := L.val.obj (op (V ⊓ W))) hvinv huv _
  obtain ⟨s, hsV, hsW⟩ := exists_sections_eval_eq L V W hcover _ _ hab
  refine nonempty_iso_unit_of_bijective_smul_on_cover L s (fun i : Bool => if i then V else W)
    (by simp [IsOpenCover, iSup_bool_eq, hcover]) fun i V' hV' => ?_
  have hev : ∀ (T : Opens X.carrier) (T' : Opens X.carrier) (hT : T' ≤ T),
      s.eval (op T') = L.val.map (homOfLE hT).op (s.eval (op T)) := by
    intro T T' hT
    exact (PresheafOfModules.sections_property s (homOfLE hT).op).symm
  cases i
  · simp only [Bool.false_eq_true, ite_false] at hV'
    rw [hev W V' hV', hsW]
    exact bijective_smul_units_smul L W b hb v⁻¹ V' hV'
  · simp only [ite_true] at hV'
    rw [hev V V' hV', hsV]
    exact bijective_smul_units_smul L V a ha u V' hV'

/-- **Multiplication by a trivializing section turns the restriction maps of `L` into those of
`𝒪_X`.** So a restriction map of `L` between two opens on which `L` is trivialized by compatible
sections is bijective as soon as the corresponding restriction map of `𝒪_X` is. -/
theorem bijective_map_of_bijective_smul (P Q : Opens X.carrier) (hQP : Q ≤ P)
    (aP : L.val.obj (op P)) (aQ : L.val.obj (op Q))
    (haQ : L.val.map (homOfLE hQP).op aP = aQ)
    (hP : Function.Bijective fun c : X.presheaf.obj (op P) => c • aP)
    (hQ : Function.Bijective fun c : X.presheaf.obj (op Q) => c • aQ)
    (h : Function.Bijective (X.presheaf.map (homOfLE hQP).op).hom) :
    Function.Bijective (L.val.map (homOfLE hQP).op).hom := by
  have hcomp : ((L.val.map (homOfLE hQP).op).hom ∘
        fun c : X.presheaf.obj (op P) => c • aP)
      = (fun c : X.presheaf.obj (op Q) => c • aQ) ∘ (X.presheaf.map (homOfLE hQP).op).hom := by
    funext c
    exact (map_smul_restrict L hQP c aP).trans (congrArg (fun y => _ • y) haQ)
  have h1 : Function.Bijective ((L.val.map (homOfLE hQP).op).hom ∘
      fun c : X.presheaf.obj (op P) => c • aP) := by
    rw [hcomp]; exact hQ.comp h
  exact (Function.Bijective.of_comp_iff _ hP).mp h1

end RingedSpace

end Stacks.SheafOfModules

namespace Stacks.PicardGroup

open Stacks.SheafOfModules

variable {Y : Scheme.{u}}

/-- Triviality of `Pic(Y)` is exactly triviality of every invertible `𝒪_Y`-module. -/
theorem isTrivial_of_subsingleton
    (hPic : Subsingleton (PicardGroup Y.presheaf Y.ringCatSheaf.2))
    (L : Y.Modules) (hL : IsInvertible Y.presheaf Y.ringCatSheaf.2 L) :
    IsTrivial Y.presheaf Y.ringCatSheaf.2 L :=
  (picardClass_eq_zero_iff Y.presheaf Y.ringCatSheaf.2 L hL).1 (Subsingleton.elim _ _)

/-- **Triviality of the Picard group transports along an isomorphism of schemes.** -/
theorem subsingleton_of_iso {X : Scheme.{u}} (e : X ≅ Y)
    (hX : Subsingleton (PicardGroup X.presheaf X.ringCatSheaf.2)) :
    Subsingleton (PicardGroup Y.presheaf Y.ringCatSheaf.2) := by
  refine subsingleton_picardGroup Y.presheaf Y.ringCatSheaf.2 fun L hL => ?_
  have := hL
  obtain ⟨φ⟩ := isTrivial_of_subsingleton hX ((Scheme.Modules.pullback e.hom).obj L)
    (Stacks.Modules.isInvertible_pullback e.hom L)
  exact ⟨((Scheme.Modules.pullbackId Y).app L).symm ≪≫
    ((Scheme.Modules.pullbackCongr e.inv_hom_id).app L).symm ≪≫
    ((Scheme.Modules.pullbackComp e.inv e.hom).app L).symm ≪≫
    (Scheme.Modules.pullback e.inv).mapIso φ ≪≫
    AlgebraicGeometry.Scheme.Modules.pullbackUnitIso e.inv⟩

/-- **A trivialization of `L` over an open subscheme with trivial Picard group**, in the
localized-site spelling that `Stacks.SheafOfModules.exists_bijective_smul_of_over_iso_unit`
consumes. -/
noncomputable def overIsoUnitOfSubsingleton (L : Y.Modules)
    [IsInvertible Y.presheaf (structureSheafRing Y.toRingedSpace).property L] (T : Y.Opens)
    (hPic : Subsingleton (PicardGroup T.toScheme.presheaf T.toScheme.ringCatSheaf.2)) :
    L.over T ≅ SheafOfModules.unit (Y.ringCatSheaf.over T) :=
  Stacks.Modules.overIsoUnitOfRestrictIsoUnit L T
    ((Scheme.Modules.restrictFunctorIsoPullback T.ι).app L ≪≫
      (isTrivial_of_subsingleton hPic ((Scheme.Modules.pullback T.ι).obj L)
        (Stacks.Modules.isInvertible_pullback T.ι L)).some)

/-- The Picard group of the empty scheme is trivial. -/
theorem subsingleton_of_isEmpty (hY : IsEmpty Y) :
    Subsingleton (PicardGroup Y.presheaf Y.ringCatSheaf.2) := by
  refine subsingleton_picardGroup Y.presheaf Y.ringCatSheaf.2 fun L _ => ?_
  refine nonempty_iso_unit_of_bijective_smul_on_cover (X := Y.toRingedSpace) L
    (PresheafOfModules.sectionsMk (fun _ => 0) (fun _ _ _ => map_zero _))
    (fun _ : Y => (⊥ : Y.Opens)) ?_ fun i => hY.elim i
  exact le_antisymm le_top fun x _ => hY.elim x

/-- **The unit of the restriction–pushforward adjunction at an invertible module is an
isomorphism** as soon as regular functions extend uniquely from `V ∩ W` to `V` for every open
`V`. On a trivializing open the restriction maps of `L` are those of `𝒪_Y`, by
`Stacks.SheafOfModules.bijective_map_of_bijective_smul`, and the trivializing opens cover `Y`. -/
theorem isIso_restrictAdjunction_unit (W : Y.Opens) (L : Y.Modules)
    [IsInvertible Y.presheaf (structureSheafRing Y.toRingedSpace).property L]
    (h : ∀ V : Y.Opens, Function.Bijective
      (Y.presheaf.map (homOfLE (W.ι.image_preimage_le V)).op).hom) :
    IsIso ((Scheme.Modules.restrictAdjunction W.ι).unit.app L) := by
  obtain ⟨T, hT, hiso⟩ := Stacks.Modules.exists_restrict_iso_unit_of_isInvertible L
  have hcover : IsOpenCover T := by
    refine le_antisymm le_top fun y _ => ?_
    have : y ∈ (⨆ z, T z) := by rw [hT]; exact Opens.mem_top y
    exact this
  choose a ha using fun y : Y => exists_bijective_smul_of_over_iso_unit (X := Y.toRingedSpace) L
    (T y) (Stacks.Modules.overIsoUnitOfRestrictIsoUnit L (T y) (hiso y).some)
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ?_
  refine bijective_app_of_bijective_on_cover (X := Y.toRingedSpace) _ T hcover ?_ V
  intro y P hP
  have hQP : W.ι ''ᵁ W.ι ⁻¹ᵁ P ≤ P := W.ι.image_preimage_le P
  exact bijective_map_of_bijective_smul (X := Y.toRingedSpace) L P _ hQP
    (L.val.map (homOfLE hP).op (a y)) (L.val.map (homOfLE (hQP.trans hP)).op (a y))
    (map_restrict_comp (X := Y.toRingedSpace) L hQP hP (a y))
    (ha y P hP) (ha y _ (hQP.trans hP)) (h P)

/-- **Descent of triviality of the Picard group along an open on which regular functions
extend.** If `Pic(W)` is trivial and, for every open `V` of `Y`, every regular function on
`V ∩ W` extends uniquely to `V`, then `Pic(Y)` is trivial.

This is the final step of [Stacks, Tag 0BDA]: an invertible module on `Y` is trivial on `W`, and
`L ≅ j_*j^*L` because the comparison is an isomorphism, while `j_*𝒪_W ≅ 𝒪_Y` is the
extension hypothesis. -/
theorem subsingleton_of_functions (W : Y.Opens)
    (h : ∀ V : Y.Opens, Function.Bijective
      (Y.presheaf.map (homOfLE (W.ι.image_preimage_le V)).op).hom)
    (hPic : Subsingleton (PicardGroup W.toScheme.presheaf W.toScheme.ringCatSheaf.2)) :
    Subsingleton (PicardGroup Y.presheaf Y.ringCatSheaf.2) := by
  refine subsingleton_picardGroup Y.presheaf Y.ringCatSheaf.2 fun L hL => ?_
  have hL' : IsInvertible Y.presheaf (structureSheafRing Y.toRingedSpace).property L := hL
  have hE : IsInvertible Y.presheaf (structureSheafRing Y.toRingedSpace).property
      (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) := isInvertible_unit _ _
  have h1 := isIso_restrictAdjunction_unit W L h
  have h2 := isIso_restrictAdjunction_unit W (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) h
  obtain ⟨φ⟩ := isTrivial_of_subsingleton hPic ((Scheme.Modules.pullback W.ι).obj L)
    (Stacks.Modules.isInvertible_pullback W.ι L)
  have e : Scheme.Modules.restrict L W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf :=
    (Scheme.Modules.restrictFunctorIsoPullback W.ι).app L ≪≫ φ
  exact ⟨(@asIso _ _ _ _ ((Scheme.Modules.restrictAdjunction W.ι).unit.app L) h1) ≪≫
    (Scheme.Modules.pushforward W.ι).mapIso
      (e ≪≫ (Scheme.Modules.restrictUnitIso W.ι).symm) ≪≫
    (@asIso _ _ _ _ ((Scheme.Modules.restrictAdjunction W.ι).unit.app
      (SheafOfModules.unit Y.ringCatSheaf : Y.Modules)) h2).symm⟩

/-- **Triviality of the Picard group from a two-open cover by opens with trivial Picard group**,
provided every unit on the intersection splits as a product of units on the two opens. -/
theorem subsingleton_of_two_opens (V W : Y.Opens) (hcover : V ⊔ W = ⊤)
    (hV : Subsingleton (PicardGroup V.toScheme.presheaf V.toScheme.ringCatSheaf.2))
    (hW : Subsingleton (PicardGroup W.toScheme.presheaf W.toScheme.ringCatSheaf.2))
    (hsplit : ∀ w : (Y.presheaf.obj (op (V ⊓ W)))ˣ,
      ∃ (u : (Y.presheaf.obj (op V))ˣ) (v : (Y.presheaf.obj (op W))ˣ),
        Y.presheaf.map (homOfLE (inf_le_left : V ⊓ W ≤ V)).op (u : Y.presheaf.obj (op V)) *
            Y.presheaf.map (homOfLE (inf_le_right : V ⊓ W ≤ W)).op (v : Y.presheaf.obj (op W))
          = (w : Y.presheaf.obj (op (V ⊓ W)))) :
    Subsingleton (PicardGroup Y.presheaf Y.ringCatSheaf.2) := by
  refine subsingleton_picardGroup Y.presheaf Y.ringCatSheaf.2 fun L hL => ?_
  have hL' : IsInvertible Y.presheaf (structureSheafRing Y.toRingedSpace).property L := hL
  obtain ⟨a, ha⟩ := exists_bijective_smul_of_over_iso_unit (X := Y.toRingedSpace) L V
    (overIsoUnitOfSubsingleton L V hV)
  obtain ⟨b, hb⟩ := exists_bijective_smul_of_over_iso_unit (X := Y.toRingedSpace) L W
    (overIsoUnitOfSubsingleton L W hW)
  exact nonempty_iso_unit_of_two_opens (X := Y.toRingedSpace) L V W hcover a ha b hb hsplit

end Stacks.PicardGroup

end
