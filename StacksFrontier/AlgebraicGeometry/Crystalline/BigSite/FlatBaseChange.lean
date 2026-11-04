module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import StacksFrontier.Algebra.Category.Ring.PushoutTensorComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Crystalline.BasisCriteria
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.Basic
public import StacksFrontier.AlgebraicGeometry.Crystalline.SpecDividedPowerScheme
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Stability

/-!
# Flat base change in the big crystalline category

Fix a global crystalline situation: a prime `p`, a divided power scheme `(S, I, γ)` over `ℤ_(p)`
and a scheme `X` over `S₀ = V(I)` on which `p` is locally nilpotent.  A fibre square

```
(U₃, T₃, δ₃) ⟶ (U₂, T₂, δ₂)
     ↓               ↓
(U₁, T₁, δ₁) ⟶ (U,  T,  δ)
```

of divided power thickenings of `X` relative to `(S, I, γ)` need not have a cartesian square of
ambient schemes, because the fibre product in `CRIS(X/S)` is computed with a divided power
envelope.  It does when `T₂ ⟶ T` is flat and `U₂ = T₂ ×_T U`: divided powers extend uniquely
along a flat ring map, so the scheme `T₁ ×_T T₂` carries a divided power structure making it an
object of `CRIS(X/S)`, and that object has the universal property of the fibre product.

## Main results

* `Crystalline.GlobalCrystallineSituation.Thickening.isPullback_targetHom_of_flat` — for a fibre
  square of divided power thickenings of `X` relative to `(S, I, γ)` whose map `T₂ ⟶ T` is flat
  and satisfies `U₂ = T₂ ×_T U`, the square of ambient schemes is cartesian,
  [Stacks, Tag 07IA].

## Implementation notes

The flat base change `T₁ ×_T T₂` is given divided powers chart by chart: on a pair of affine
opens the defining ideal of the thickening `U₁ ×_U U₂ ↪ T₁ ×_T T₂` is the image of the defining
ideal of `U ↪ T`, so the chosen extension of divided powers along a flat ring map,
`DividedPowers.DividedPowerRing.extendedDividedPowersOfMapEqBotOrIsPrincipalOrFlat`, supplies
divided powers on it, and uniqueness of the flat extension makes the charts agree.  The
charts are glued by extending a morphism of sheaves of types from a basis of opens, which is why
the divided power operations are built as a single endomorphism of the ideal sheaf for each
degree rather than open by open.

The defining ideal of a closed immersion is used as an ideal subsheaf of the structure sheaf
rather than as Mathlib's `AlgebraicGeometry.Scheme.IdealSheafData`, since that is the shape a
divided power structure is carried on; it is the sectionwise kernel of the structure map, and on
affine opens it agrees with `AlgebraicGeometry.Scheme.Hom.ker`.

The conclusion keeps the projections of the given square rather than merely asserting an
abstract isomorphism of schemes, and both hypotheses are stated as cartesian squares of the
actual morphisms.

## References

* [Stacks Project, Tag 07IA](https://stacks.math.columbia.edu/tag/07IA)
* [Stacks Project, Tag 07H1](https://stacks.math.columbia.edu/tag/07H1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace Crystalline

open _root_.DividedPowers.DividedPowerRing

variable {S : GlobalCrystallineSituation.{u}}
variable {A B C D : GlobalCrystallineSituation.Thickening S}

/-- A flat extension of a divided power ring carries the uniquely determined
divided powers on the extended ideal. -/
private noncomputable def flatExtendedDividedPowers
    (R : DividedPowerRing.{u}) {T : Type u} [CommRing T]
    (f : R.carrier →+* T) (hf : f.Flat) :
    _root_.DividedPowers (R.ideal.map f) :=
  extendedDividedPowersOfMapEqBotOrIsPrincipalOrFlat
    R f (Or.inr (.inr hf))

/-- The extension map into a flat extension is a divided power morphism. -/
private theorem isDPMorphism_flatExtendedDividedPowers
    (R : DividedPowerRing.{u}) {T : Type u} [CommRing T]
    (f : R.carrier →+* T) (hf : f.Flat) :
    _root_.DividedPowers.IsDPMorphism R.dividedPowers (flatExtendedDividedPowers R f hf) f :=
  isDPMorphism_extendedDividedPowersOfMapEqBotOrIsPrincipalOrFlat R f (Or.inr (.inr hf))

/-- The divided power structure on a flat extension of a divided power ideal for which the
extension map is a divided power morphism is unique. -/
private theorem flatExtendedDividedPowers_unique
    (R : DividedPowerRing.{u}) {T : Type u} [CommRing T]
    (f : R.carrier →+* T) (hf : f.Flat)
    (δ : _root_.DividedPowers (R.ideal.map f))
    (hδ : _root_.DividedPowers.IsDPMorphism R.dividedPowers δ f) :
    δ = flatExtendedDividedPowers R f hf := by
  obtain ⟨_, _, huniq⟩ :=
    DividedPowers.existsUnique_extension
      R.dividedPowers f
      ⟨flatExtendedDividedPowers R f hf, isDPMorphism_flatExtendedDividedPowers R f hf⟩
  exact (huniq δ hδ).trans (huniq _ (isDPMorphism_flatExtendedDividedPowers R f hf)).symm

/-- A ring map out of a flat extension of a divided power ideal is a divided power morphism as
soon as its composite with the extension map is one, even when the target divided power ideal is
larger than the image of the extended ideal. -/
private theorem flatExtendedDividedPowers_map_to
    (R : DividedPowerRing.{u}) {T : Type u} [CommRing T]
    (f : R.carrier →+* T) (hf : f.Flat)
    {U : Type u} [CommRing U] (J : Ideal U)
    (δ : _root_.DividedPowers J) (g : T →+* U)
    (hδ : _root_.DividedPowers.IsDPMorphism R.dividedPowers δ (g.comp f)) :
    _root_.DividedPowers.IsDPMorphism (flatExtendedDividedPowers R f hf) δ g := by
  apply _root_.DividedPowers.IsDPMorphism.of_comp
    (hI := R.dividedPowers) (hJ := flatExtendedDividedPowers R f hf)
    (hK := δ) (f := f) (g := g)
  · simp
  · exact isDPMorphism_flatExtendedDividedPowers R f hf
  · exact hδ

/-- Transport divided-power compatibility across an equality of ideals. -/
private theorem dpMorphism_transport_ideal
    {R T : Type u} [CommRing R] [CommRing T]
    {I : Ideal R} {J K : Ideal T} (e : J = K)
    {γ : _root_.DividedPowers I} {δ : _root_.DividedPowers J}
    (f : R →+* T)
    (h : _root_.DividedPowers.IsDPMorphism γ δ f) :
    _root_.DividedPowers.IsDPMorphism γ (e ▸ δ) f := by
  cases e
  exact h

/-- Remove transport of the source divided-power ideal from a morphism. -/
private theorem dpMorphism_untransport_source_ideal
    {R T : Type u} [CommRing R] [CommRing T]
    {I J : Ideal R} (e : I = J) {K : Ideal T}
    {γ : _root_.DividedPowers I} {δ : _root_.DividedPowers K}
    (f : R →+* T)
    (h : _root_.DividedPowers.IsDPMorphism (e ▸ γ) δ f) :
    _root_.DividedPowers.IsDPMorphism γ δ f := by
  cases e
  exact h

/-- The flat extension of divided powers, packaged as a divided power ring. -/
private noncomputable def flatExtendedDividedPowerRing
    (C : DividedPowerRing.{u}) {T : Type u} [CommRing T]
    (q : C.carrier →+* T) (hq : q.Flat) : DividedPowerRing.{u} :=
  { carrier := T
    ideal := C.ideal.map q
    dividedPowers := flatExtendedDividedPowers C q hq }

/-- Maps into a flat extension preserve its divided powers when their composites
from the original base agree. -/
private theorem flatExtendedDividedPowerRing_maps
    {R B C : DividedPowerRing.{u}}
    (f : R ⟶ B) (g : R ⟶ C)
    (hf : f.toRingHom.Flat)
    (hB : B.ideal = R.ideal.map f.toRingHom)
    {T : Type u} [CommRing T]
    (p : B.carrier →+* T) (q : C.carrier →+* T) (hq : q.Flat)
    (hpq : p.comp f.toRingHom = q.comp g.toRingHom) :
    _root_.DividedPowers.IsDPMorphism B.dividedPowers
      (flatExtendedDividedPowerRing C q hq).dividedPowers p ∧
    _root_.DividedPowers.IsDPMorphism C.dividedPowers
      (flatExtendedDividedPowerRing C q hq).dividedPowers q := by
  have hq' := isDPMorphism_flatExtendedDividedPowers C q hq
  refine ⟨?_, hq'⟩
  have hfB : _root_.DividedPowers.IsDPMorphism R.dividedPowers
      (hB ▸ B.dividedPowers) f.toRingHom :=
    dpMorphism_transport_ideal hB f.toRingHom f.isDPMorphism
  have huniq := flatExtendedDividedPowers_unique R f.toRingHom hf
    (hB ▸ B.dividedPowers) hfB
  have hδ : _root_.DividedPowers.IsDPMorphism R.dividedPowers
      (flatExtendedDividedPowerRing C q hq).dividedPowers
      (p.comp f.toRingHom) := by
    rw [hpq]
    exact _root_.DividedPowers.IsDPMorphism.comp _ hq' g.isDPMorphism
  have hmap := flatExtendedDividedPowers_map_to R f.toRingHom hf
    (C.ideal.map q) (flatExtendedDividedPowerRing C q hq).dividedPowers p hδ
  have hmap' : _root_.DividedPowers.IsDPMorphism (hB ▸ B.dividedPowers)
      (flatExtendedDividedPowerRing C q hq).dividedPowers p := by
    rwa [huniq]
  exact dpMorphism_untransport_source_ideal hB p hmap'

/-- Restricting twice agrees with restricting along any morphism in the poset of opens. -/
private theorem presheaf_map_map_eq (X : Scheme.{u}) {U V W : X.Opensᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) (h : U ⟶ W) (y : X.presheaf.obj U) :
    X.presheaf.map g (X.presheaf.map f y) = X.presheaf.map h y := by
  rw [Subsingleton.elim h (f ≫ g)]
  exact (ConcreteCategory.congr_hom (X.presheaf.map_comp f g) y).symm

open Opposite TopologicalSpace in
/-- Compatible divided powers on a basis extend to the ideal sheaf. -/
private theorem exists_dividedPowerStructure_of_basis (X : Scheme.{u})
    (I : (SheafOfModules.unit X.ringCatSheaf).Submodule)
    {ι : Type u} (B : ι → X.Opens) (hB : Opens.IsBasis (Set.range B))
    (δ : ∀ k, DividedPowers (sectionIdeal X.sheaf I (op (B k))))
    (hδ : ∀ a b (f : B b ⟶ B a),
      DividedPowers.IsDPMorphism (δ a) (δ b) (X.presheaf.map f.op).hom) :
    ∃ γ : DividedPowerStructure.{u, u, u} X.sheaf I,
      ∀ k, γ.dividedPowers (op (B k)) = δ k := by
  classical
  let F := DividedPowerScheme.idealTypeSheaf X I
  let α (n : ℕ) : (inducedFunctor B).op ⋙ F.obj ⟶
      (inducedFunctor B).op ⋙ F.obj :=
    { app := fun k => TypeCat.ofHom fun x => ⟨(δ k.unop).dpow (n + 1) x.val,
          (δ k.unop).dpow_mem (Nat.succ_ne_zero n) x.property⟩
      naturality := by
        intro a b f
        ext x
        exact Subtype.ext ((hδ a.unop b.unop ((inducedFunctor B).map f.unop)).map_dpow
          x.property).symm }
  let β (n : ℕ) : F.obj ⟶ F.obj := TopCat.Sheaf.restrictHomEquivHom F.obj F hB (α n)
  have hβ (n : ℕ) (k : ι) (x : I.obj (op (B k))) :
      (β n).app (op (B k)) x = (α n).app (op k) x :=
    ConcreteCategory.congr_hom (TopCat.Sheaf.extend_hom_app F.obj F hB (α n) k) x
  let d (U : X.Opens) (n : ℕ) (x : Γ(X, U)) : Γ(X, U) :=
    if hx : x ∈ I.obj (op U) then
      match n with
      | 0 => 1
      | n + 1 => ((β n).app (op U) ⟨x, hx⟩).val
    else 0
  have hdnull (U : X.Opens) (n : ℕ) (x : Γ(X, U)) (hx : x ∉ I.obj (op U)) :
      d U n x = 0 := by simp [d, hx]
  have hdmap (U : X.Opens) (n : ℕ) (x : Γ(X, U)) (hx : x ∈ I.obj (op U))
      (k : ι) (hk : B k ≤ U) :
      X.presheaf.map (homOfLE hk).op (d U n x) =
        (δ k).dpow n (X.presheaf.map (homOfLE hk).op x) := by
    cases n with
    | zero =>
      simp only [d, dite_eq_left hx, map_one]
      exact ((δ k).dpow_zero (I.map_mem (homOfLE hk).op hx)).symm
    | succ n =>
      have hb := ConcreteCategory.congr_hom ((β n).naturality (homOfLE hk).op) ⟨x, hx⟩
      have hb' := congrArg Subtype.val hb
      change ((β n).app (op (B k)) (F.obj.map (homOfLE hk).op ⟨x, hx⟩)).val =
        X.presheaf.map (homOfLE hk).op ((β n).app (op U) ⟨x, hx⟩).val at hb'
      have he := congrArg Subtype.val
        (hβ n k (F.obj.map (homOfLE hk).op ⟨x, hx⟩))
      change ((β n).app (op (B k)) (F.obj.map (homOfLE hk).op ⟨x, hx⟩)).val =
        (δ k).dpow (n + 1) (X.presheaf.map (homOfLE hk).op x) at he
      simp only [d, dite_eq_left hx]
      exact hb'.symm.trans he
  let γU (U : X.Opens) : DividedPowers (sectionIdeal X.sheaf I (op U)) :=
    DividedPowerScheme.dividedPowersOfSeparatingFamily _
      (fun k : {k : ι // B k ≤ U} => sectionIdeal X.sheaf I (op (B k.val)))
      (fun k => δ k.val)
      (fun k => (X.presheaf.map (homOfLE k.property).op).hom)
      (fun x y h => DividedPowerScheme.section_ext_basis X B hB (fun k hk => h ⟨k, hk⟩))
      (fun x => ⟨fun hx k => I.map_mem (homOfLE k.property).op hx,
        fun hx => (DividedPowerScheme.mem_ideal_basis X I B hB x).mpr (fun k hk => hx ⟨k, hk⟩)⟩)
      (d U) (hdnull U) (fun n x hx k => hdmap U n x hx k.val k.property)
  refine ⟨(show DividedPowerStructure.{u, u, u} X.sheaf I from
    { dividedPowers := fun U => γU U.unop, naturality := ?_ }), ?_⟩
  · intro U V f
    refine ⟨Ideal.map_le_iff_le_comap.mpr (fun x hx => I.map_mem f hx), ?_⟩
    intro n x hx
    apply DividedPowerScheme.section_ext_basis X B hB
    intro k hk
    have hUf : B k ≤ U.unop := hk.trans (leOfHom f.unop)
    have hxV : X.presheaf.map f x ∈ I.obj V := I.map_mem f hx
    show X.presheaf.map (homOfLE hk).op (d V.unop n (X.presheaf.map f x)) =
      X.presheaf.map (homOfLE hk).op (X.presheaf.map f (d U.unop n x))
    rw [hdmap _ _ _ hxV]
    simp only [← CommRingCat.comp_apply, ← Functor.map_comp]
    rw [presheaf_map_map_eq X f (homOfLE hk).op (homOfLE hUf).op x]
    exact (hdmap U.unop n x hx k hUf).symm
  · intro k
    apply DividedPowers.ext
    intro n x hx
    have hm := hdmap (B k) n x hx k le_rfl
    show d (B k) n x = (δ k).dpow n x
    have he' : X.presheaf.map (homOfLE (le_rfl : B k ≤ B k)).op =
        𝟙 Γ(X, B k) := by
      rw [show (homOfLE (le_rfl : B k ≤ B k)).op = 𝟙 (op (B k)) from Subsingleton.elim _ _]
      exact X.presheaf.map_id _
    have he'' (y : Γ(X, B k)) : X.presheaf.map (homOfLE le_rfl).op y = y := by
      rw [he']
      exact CategoryTheory.id_apply y
    simp only [he''] at hm
    apply Eq.trans hm
    congr 1
    exact he'' x

open Opposite TopologicalSpace in
/-- Flat affine extension and restriction compatibility globalize the divided
powers on the inverse-image ideal. -/
private theorem exists_dividedPowerStructure_of_flat
    (Y : DividedPowerScheme.{u}) (X : Scheme.{u})
    (f : X ⟶ Y.scheme) [Flat f]
    (I : (SheafOfModules.unit X.ringCatSheaf).Submodule)
    (hI : ∀ (V : Y.scheme.affineOpens) (W : X.affineOpens)
      (h : W.1 ≤ f ⁻¹ᵁ V.1),
      (sectionIdeal Y.scheme.sheaf Y.ideal (op V.1)).map
        (f.appLE V.1 W.1 h).hom = sectionIdeal X.sheaf I (op W.1)) :
    ∃ γ : DividedPowerStructure.{u, u, u} X.sheaf I,
      ∀ (V : Y.scheme.affineOpens) (W : X.affineOpens) (h : W.1 ≤ f ⁻¹ᵁ V.1),
        DividedPowers.IsDPMorphism (Y.dividedPowers.dividedPowers (op V.1))
          (γ.dividedPowers (op W.1)) (f.appLE V.1 W.1 h).hom := by
  classical
  let K := {c : Y.scheme.affineOpens × X.affineOpens // c.2.1 ≤ f ⁻¹ᵁ c.1.1}
  let B (c : K) : X.Opens := c.val.2.1
  have hB : Opens.IsBasis (Set.range B) := by
    rw [Opens.isBasis_iff_nbhd]
    intro U x hx
    obtain ⟨V, hV, hxV, -⟩ := Opens.isBasis_iff_nbhd.mp
      Y.scheme.isBasis_affineOpens (U := ⊤) (x := f x) trivial
    obtain ⟨W, hW, hxW, hWU⟩ := Opens.isBasis_iff_nbhd.mp
      X.isBasis_affineOpens (U := U ⊓ f ⁻¹ᵁ V) ⟨hx, hxV⟩
    refine ⟨W, ⟨⟨(⟨V, hV⟩, ⟨W, hW⟩), hWU.trans inf_le_right⟩, rfl⟩,
      hxW, hWU.trans inf_le_left⟩
  have hex (c : K) :
      ∃ δ : DividedPowers (sectionIdeal X.sheaf I (op (B c))),
        DividedPowers.IsDPMorphism (Y.dividedPowers.dividedPowers (op c.val.1.1))
          δ (f.appLE c.val.1.1 (B c) c.property).hom := by
    let R := Y.dividedPowers.toDividedPowerRing (op c.val.1.1)
    have he := dividedPowers_extends_of_map_eq_bot_or_isPrincipal_or_flat R
        (f.appLE c.val.1.1 (B c) c.property).hom
        (Or.inr (Or.inr (f.flat_appLE c.val.1.2 c.val.2.2 c.property)))
    change ∃ δ : DividedPowers
      ((sectionIdeal Y.scheme.sheaf Y.ideal (op c.val.1.1)).map
        (f.appLE c.val.1.1 (B c) c.property).hom),
      DividedPowers.IsDPMorphism (Y.dividedPowers.dividedPowers (op c.val.1.1))
        δ (f.appLE c.val.1.1 (B c) c.property).hom at he
    rwa [hI c.val.1 c.val.2 c.property] at he
  choose δ hδ using hex
  have hres (a b : K) (hV : b.val.1.1 ≤ a.val.1.1) (hW : B b ≤ B a) :
      DividedPowers.IsDPMorphism (δ a) (δ b)
        (X.presheaf.map (homOfLE hW).op).hom := by
    apply DividedPowers.IsDPMorphism.of_comp
      (hI := Y.dividedPowers.dividedPowers (op a.val.1.1))
      (f := (f.appLE a.val.1.1 (B a) a.property).hom)
    · exact (hI a.val.1 a.val.2 a.property).symm
    · exact hδ a
    · have he := DividedPowers.IsDPMorphism.comp (δ b) (hδ b)
        (Y.dividedPowers.naturality (homOfLE hV).op)
      have hcomp : (X.presheaf.map (homOfLE hW).op).hom.comp
          (f.appLE a.val.1.1 (B a) a.property).hom =
        (f.appLE b.val.1.1 (B b) b.property).hom.comp
          (Y.scheme.presheaf.map (homOfLE hV).op).hom := by
        simp only [← CommRingCat.hom_comp, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
      exact isDPMorphism_of_eq hcomp.symm he
  have hnat (a b : K) (r : B b ⟶ B a) :
      DividedPowers.IsDPMorphism (δ a) (δ b) (X.presheaf.map r.op).hom := by
    refine ⟨Ideal.map_le_iff_le_comap.mpr (fun x hx => I.map_mem r.op hx), ?_⟩
    intro n x hx
    apply TopCat.Presheaf.IsSheaf.section_ext X.sheaf.property
    intro z hz
    have hza : z ∈ B a := leOfHom r hz
    have hzV : f z ∈ a.val.1.1 ⊓ b.val.1.1 := ⟨a.property hza, b.property hz⟩
    obtain ⟨V, hV, hzV, hVU⟩ := Opens.isBasis_iff_nbhd.mp
      Y.scheme.isBasis_affineOpens hzV
    obtain ⟨W, hW, hzW, hWU⟩ := Opens.isBasis_iff_nbhd.mp
      X.isBasis_affineOpens (U := B b ⊓ f ⁻¹ᵁ V) ⟨hz, hzV⟩
    let c : K := ⟨(⟨V, hV⟩, ⟨W, hW⟩), hWU.trans inf_le_right⟩
    have hcb : B c ≤ B b := hWU.trans inf_le_left
    have hca : B c ≤ B a := hcb.trans (leOfHom r)
    have hac := hres a c (hVU.trans inf_le_left) hca
    have hbc := hres b c (hVU.trans inf_le_right) hcb
    have hecomp := presheaf_map_map_eq X r.op (homOfLE hcb).op (homOfLE hca).op
    refine ⟨W, hcb, hzW, ?_⟩
    show X.presheaf.map (homOfLE hcb).op ((δ b).dpow n (X.presheaf.map r.op x)) =
      X.presheaf.map (homOfLE hcb).op (X.presheaf.map r.op ((δ a).dpow n x))
    exact (hbc.map_dpow (n := n) (I.map_mem r.op hx)).trans
      ((congrArg ((δ c).dpow n) (hecomp x)).trans
        ((hac.map_dpow (n := n) hx).symm.trans (hecomp ((δ a).dpow n x)).symm))
  obtain ⟨γ, hγ⟩ := exists_dividedPowerStructure_of_basis X I B hB δ hnat
  refine ⟨γ, fun V W h => ?_⟩
  have he := hδ (⟨(V, W), h⟩ : K)
  rwa [← hγ ⟨(V, W), h⟩] at he

open RingedSpaceModuleAdjunction in
/-- The defining ideal subsheaf of a scheme morphism. -/
noncomputable abbrev definingIdeal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (SheafOfModules.unit Y.ringCatSheaf).Submodule :=
  Stacks.SheafOfModules.kerSubmodule (SheafOfModules.unitToPushforwardObjUnit
    (structureSheafHom f.toLRSHom.toShHom))

open RingedSpaceModuleAdjunction in
/-- The defining ideal of a closed immersion is quasi-coherent. -/
theorem definingIdeal_isQuasicoherent {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsClosedImmersion f] :
    (definingIdeal f).toSheafOfModules.IsQuasicoherent := by
  have hq := ((Stacks.AlgebraicGeometry.ClosedImmersionTFAE.closedImmersion_tfae f).out 1 5).mp
    (show IsClosedImmersion f from inferInstance)
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    (((Stacks.SheafOfModules.isLimitKernelForkKerSubmodule
      (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom f.toLRSHom.toShHom))).conePointUniqueUpToIso
      (limit.isLimit _))).symm hq.2

open Opposite in
/-- On an affine open the defining ideal is the scheme-theoretic kernel ideal. -/
theorem definingIdeal_obj {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] (V : Y.affineOpens) :
    (definingIdeal f).obj (op V.1) = f.ker.ideal V := by
  rw [Scheme.Hom.ker_apply]
  rfl

open Opposite TopologicalSpace in
/-- On affine charts, base change extends the defining ideal of a closed immersion. -/
private theorem definingIdeal_map_of_isPullback
    {X₀ X Y₀ Y : Scheme.{u}} (iX : X₀ ⟶ X) (iY : Y₀ ⟶ Y)
    (f : Y ⟶ X) (g : Y₀ ⟶ X₀) [IsClosedImmersion iX] [IsClosedImmersion iY]
    (h : IsPullback iY g f iX)
    (V : X.affineOpens) (W : Y.affineOpens) (hW : W.1 ≤ f ⁻¹ᵁ V.1) :
    (sectionIdeal X.sheaf (definingIdeal iX) (op V.1)).map
      (f.appLE V.1 W.1 hW).hom =
      (definingIdeal iY).obj (op W.1) := by
  have hle : iY ⁻¹ᵁ W.1 ≤ g ⁻¹ᵁ (iX ⁻¹ᵁ V.1) := by
    intro z hz
    have hz' := hW hz
    have he := congrArg (fun k : Y₀ ⟶ X => k z) h.w
    change f (iY z) = iX (g z) at he
    show iX (g z) ∈ V.1
    rwa [← he]
  have hUY : iY ⁻¹ᵁ W.1 = g ⁻¹ᵁ (iX ⁻¹ᵁ V.1) ⊓ iY ⁻¹ᵁ W.1 :=
    (inf_eq_right.mpr hle).symm
  have hp := (isIso_pushoutSection_iff h.flip hW le_rfl hUY).mp
    (isIso_pushoutSection_of_isAffineOpen h.flip hW le_rfl hUY
      V.2 W.2 (V.2.preimage iX))
  have he := CommRingCat.ker_inr_of_isPushout _ _ _ _ hp
    (by simpa [Scheme.Hom.appLE] using iX.app_surjective V.1 V.2)
  show Ideal.map _ ((definingIdeal iX).obj (op V.1) : Ideal Γ(X, V.1)) = _
  rw [definingIdeal_obj iX V, definingIdeal_obj iY W, Scheme.Hom.ker_apply,
    Scheme.Hom.ker_apply]
  rw [Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_eq_app] at he
  exact he.symm

open Opposite TopologicalSpace in
/-- Divided power compatibility can be verified on neighborhoods of each point. -/
private theorem isDPMorphism_app_of_locally
    (X Y : DividedPowerScheme.{u}) (f : X.scheme ⟶ Y.scheme)
    (hloc : ∀ (U : Y.scheme.Opens) (z : X.scheme), z ∈ f ⁻¹ᵁ U →
      ∃ (V : Y.scheme.Opens) (W : X.scheme.Opens) (_hV : V ≤ U)
        (hW : W ≤ f ⁻¹ᵁ V), z ∈ W ∧
        DividedPowers.IsDPMorphism (Y.dividedPowers.dividedPowers (op V))
          (X.dividedPowers.dividedPowers (op W)) (f.appLE V W hW).hom)
    (U : Y.scheme.Opens) :
    DividedPowers.IsDPMorphism (Y.dividedPowers.dividedPowers (op U))
      (X.dividedPowers.dividedPowers (op (f ⁻¹ᵁ U))) (f.app U).hom := by
  have hmap (V : Y.scheme.Opens) (W : X.scheme.Opens)
      (hV : V ≤ U) (hW : W ≤ f ⁻¹ᵁ V)
      (hm : DividedPowers.IsDPMorphism (Y.dividedPowers.dividedPowers (op V))
        (X.dividedPowers.dividedPowers (op W)) (f.appLE V W hW).hom) :
      DividedPowers.IsDPMorphism (Y.dividedPowers.dividedPowers (op U))
        (X.dividedPowers.dividedPowers (op W))
        (f.appLE U W (hW.trans ((Opens.map f.base).map (homOfLE hV)).le)).hom := by
    rw [← f.map_appLE hW (homOfLE hV).op]
    exact DividedPowers.IsDPMorphism.comp
      (X.dividedPowers.dividedPowers (op W)) hm
      (Y.dividedPowers.naturality (homOfLE hV).op)
  have hmem (x : Γ(Y.scheme, U)) (hx : x ∈ Y.ideal.obj (op U)) :
      f.app U x ∈ X.ideal.obj (op (f ⁻¹ᵁ U)) := by
    apply X.ideal.isSheaf (f.app U x)
    intro z hz
    obtain ⟨V, W, hV, hW, hzW, hm⟩ := hloc U z hz
    exact ⟨W, homOfLE (hW.trans ((Opens.map f.base).map (homOfLE hV)).le),
      (hmap V W hV hW hm).ideal_comp (Ideal.mem_map_of_mem _ hx), hzW⟩
  refine ⟨Ideal.map_le_iff_le_comap.mpr hmem, ?_⟩
  intro n x hx
  apply TopCat.Presheaf.IsSheaf.section_ext X.scheme.sheaf.property
  intro z hz
  obtain ⟨V, W, hV, hW, hzW, hm⟩ := hloc U z hz
  have hWU := hW.trans ((Opens.map f.base).map (homOfLE hV)).le
  refine ⟨W, hWU, hzW, ?_⟩
  exact ((X.dividedPowers.naturality (homOfLE hWU).op).map_dpow (n := n)
    (hmem x hx)).trans ((hmap V W hV hW hm).map_dpow (n := n) hx).symm

open Opposite in
/-- A divided power morphism preserves divided powers on restricted sections. -/
private theorem isDPMorphism_appLE
    {X Y : DividedPowerScheme.{u}} (f : X ⟶ Y)
    (V : Y.scheme.Opens) (W : X.scheme.Opens) (hW : W ≤ f.hom ⁻¹ᵁ V) :
    DividedPowers.IsDPMorphism (Y.dividedPowers.dividedPowers (op V))
      (X.dividedPowers.dividedPowers (op W)) (f.hom.appLE V W hW).hom :=
  DividedPowers.IsDPMorphism.comp _
    (X.dividedPowers.naturality (homOfLE hW).op) (f.compatible V)

open Opposite in
/-- A scheme morphism equal to the underlying morphism of a map of divided power schemes
preserves divided powers on restricted sections. -/
private theorem isDPMorphism_appLE_of_eq {X Y : DividedPowerScheme.{u}} (k : X ⟶ Y)
    (t : X.scheme ⟶ Y.scheme) (ht : t = k.hom) (V : Y.scheme.Opens) (W : X.scheme.Opens)
    (hW : W ≤ t ⁻¹ᵁ V) :
    DividedPowers.IsDPMorphism (Y.dividedPowers.dividedPowers (op V))
      (X.dividedPowers.dividedPowers (op W)) (t.appLE V W hW).hom := by
  subst ht
  exact isDPMorphism_appLE k V W hW

open Opposite TopologicalSpace in
/-- A scheme map over a cartesian morphism of thickenings preserves divided
powers whenever its composite does. -/
private theorem isDPMorphism_app_of_comp_cartesian
    (A B : SchemeThickening.{u})
    (f : B.target ⟶ A.target) (s : B.source ⟶ A.source)
    (h : IsPullback B.immersion s f.hom A.immersion)
    (X : DividedPowerScheme.{u}) (t : X.scheme ⟶ B.target.scheme)
    (k : X ⟶ A.target) (hk : t ≫ f.hom = k.hom)
    (U : B.target.scheme.Opens) :
    DividedPowers.IsDPMorphism (B.target.dividedPowers.dividedPowers (op U))
      (X.dividedPowers.dividedPowers (op (t ⁻¹ᵁ U))) (t.app U).hom := by
  apply isDPMorphism_app_of_locally X B.target t
  intro U z hz
  obtain ⟨V₀, hV₀, hzV₀, -⟩ := Opens.isBasis_iff_nbhd.mp
    A.target.scheme.isBasis_affineOpens (U := ⊤) (x := f.hom (t z)) trivial
  obtain ⟨V, hV, hzV, hVU⟩ := Opens.isBasis_iff_nbhd.mp
    B.target.scheme.isBasis_affineOpens (U := U ⊓ f.hom ⁻¹ᵁ V₀) ⟨hz, hzV₀⟩
  obtain ⟨W, hW, hzW, hWV⟩ := Opens.isBasis_iff_nbhd.mp
    X.scheme.isBasis_affineOpens (U := t ⁻¹ᵁ V) (x := z) hzV
  refine ⟨V, W, hVU.trans inf_le_left, hWV, hzW, ?_⟩
  apply DividedPowers.IsDPMorphism.of_comp
    (hI := A.target.dividedPowers.dividedPowers (op V₀))
    (f := (f.hom.appLE V₀ V (hVU.trans inf_le_right)).hom)
  · show (B.target.ideal.obj (op V) : Ideal Γ(B.target.scheme, V)) = _
    have he := definingIdeal_map_of_isPullback A.immersion B.immersion f.hom s h
      ⟨V₀, hV₀⟩ ⟨V, hV⟩ (hVU.trans inf_le_right)
    change Ideal.map _ ((definingIdeal A.immersion).obj (op V₀) :
      Ideal Γ(A.target.scheme, V₀)) = _ at he
    rw [definingIdeal_obj A.immersion ⟨V₀, hV₀⟩,
      definingIdeal_obj B.immersion ⟨V, hV⟩,
      ← A.ideal_eq_ker ⟨V₀, hV₀⟩, ← B.ideal_eq_ker ⟨V, hV⟩] at he
    exact he.symm
  · exact isDPMorphism_appLE f V₀ V (hVU.trans inf_le_right)
  · have hle : W ≤ (t ≫ f.hom) ⁻¹ᵁ V₀ :=
      hWV.trans ((Opens.map t.base).map (homOfLE (hVU.trans inf_le_right))).le
    have hmap : (t.appLE V W hWV).hom.comp
        (f.hom.appLE V₀ V (hVU.trans inf_le_right)).hom =
          ((t ≫ f.hom).appLE V₀ W hle).hom := by
      rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
    exact isDPMorphism_of_eq hmap.symm
      (isDPMorphism_appLE_of_eq k (t ≫ f.hom) hk V₀ W hle)

open Opposite in
/-- Flat base change of a thickening carries divided powers extending those of
the original thickening on every affine chart. -/
private theorem exists_dividedPowerStructure_baseChange
    (C : SchemeThickening.{u}) (P : Scheme.{u})
    (q : P ⟶ C.target.scheme) [Flat q] :
    ∃ γ : DividedPowerStructure.{u, u, u} P.sheaf
      (definingIdeal (pullback.snd C.immersion q)),
      ∀ (V : C.target.scheme.affineOpens) (W : P.affineOpens)
        (h : W.1 ≤ q ⁻¹ᵁ V.1),
        DividedPowers.IsDPMorphism (C.target.dividedPowers.dividedPowers (op V.1))
          (γ.dividedPowers (op W.1)) (q.appLE V.1 W.1 h).hom := by
  apply exists_dividedPowerStructure_of_flat
  intro V W hW
  show Ideal.map _ (C.target.ideal.obj (op V.1) : Ideal Γ(C.target.scheme, V.1)) = _
  rw [C.ideal_eq_ker V, ← definingIdeal_obj C.immersion V]
  exact definingIdeal_map_of_isPullback C.immersion (pullback.snd C.immersion q)
    q (pullback.fst C.immersion q) (IsPullback.of_hasPullback _ _).flip V W hW

/-- The ordinary flat base change, with divided powers obtained by affine
extension and gluing. -/
private noncomputable def flatBaseChangeThickening
    (C : SchemeThickening.{u}) {P : Scheme.{u}}
    (q : P ⟶ C.target.scheme) [Flat q] : SchemeThickening.{u} where
  source := pullback C.immersion q
  target :=
    { scheme := P
      ideal := definingIdeal (pullback.snd C.immersion q)
      isQuasicoherent := definingIdeal_isQuasicoherent _
      dividedPowers := (exists_dividedPowerStructure_baseChange C P q).choose }
  immersion := pullback.snd C.immersion q
  isThickening := Stacks.Thickenings.isThickening_isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback C.immersion q) C.isThickening
  ideal_eq_ker := definingIdeal_obj _

/-- The projection from a flat base change preserves divided powers. -/
private noncomputable def flatBaseChangeProjection
    (C : SchemeThickening.{u}) {P : Scheme.{u}}
    (q : P ⟶ C.target.scheme) [Flat q] :
    (flatBaseChangeThickening C q).target ⟶ C.target where
  hom := q
  compatible := DividedPowerScheme.isDPMorphism_app_of_affine
    (flatBaseChangeThickening C q).target C.target q
    (exists_dividedPowerStructure_baseChange C P q).choose_spec

/-- The immersion and the two projections in a flat base change commute. -/
private theorem flatBaseChangeProjection_naturality
    (C : SchemeThickening.{u}) {P : Scheme.{u}}
    (q : P ⟶ C.target.scheme) [Flat q] :
    (flatBaseChangeThickening C q).immersion ≫ (flatBaseChangeProjection C q).hom =
      pullback.fst C.immersion q ≫ C.immersion := pullback.condition.symm

/-- Flat base change, with the inherited maps to the crystalline base and to `X`. -/
private noncomputable def flatBaseChangeCrystalline
    (C : GlobalCrystallineSituation.Thickening S) {P : Scheme.{u}}
    (q : P ⟶ C.thickening.target.scheme) [Flat q] :
    GlobalCrystallineSituation.Thickening S where
  thickening := flatBaseChangeThickening C.thickening q
  toBase := flatBaseChangeProjection C.thickening q ≫ C.toBase
  toX := pullback.fst C.thickening.immersion q ≫ C.toX
  over_base := by
    change pullback.snd C.thickening.immersion q ≫ q ≫ C.toBase.hom = _
    rw [← Category.assoc, ← pullback.condition, Category.assoc, C.over_base]
    exact (Category.assoc _ _ _).symm

/-- The projection to the original object is a crystalline morphism. -/
private noncomputable def flatBaseChangeCrystallineProjection
    (C : GlobalCrystallineSituation.Thickening S) {P : Scheme.{u}}
    (q : P ⟶ C.thickening.target.scheme) [Flat q] :
    flatBaseChangeCrystalline C q ⟶ C where
  sourceHom := pullback.fst C.thickening.immersion q
  targetHom := flatBaseChangeProjection C.thickening q
  immersion_naturality := flatBaseChangeProjection_naturality C.thickening q
  base_naturality := rfl
  toX_naturality := rfl

/-- A crystalline morphism lifts through a flat base change whenever its
ambient scheme morphism does. -/
private noncomputable def flatBaseChangeCrystallineLift
    (C D : GlobalCrystallineSituation.Thickening S) {P : Scheme.{u}}
    (q : P ⟶ C.thickening.target.scheme) [Flat q] (j : D ⟶ C)
    (t : D.thickening.target.scheme ⟶ P) (ht : t ≫ q = j.targetHom.hom) :
    D ⟶ flatBaseChangeCrystalline C q where
  sourceHom := pullback.lift j.sourceHom (D.thickening.immersion ≫ t)
    (by rw [Category.assoc, ht, j.immersion_naturality])
  targetHom :=
    { hom := t
      compatible := isDPMorphism_app_of_comp_cartesian C.thickening
        (flatBaseChangeThickening C.thickening q) (flatBaseChangeProjection C.thickening q)
        (pullback.fst C.thickening.immersion q)
        (IsPullback.of_hasPullback C.thickening.immersion q).flip
        D.thickening.target t j.targetHom ht }
  immersion_naturality := (pullback.lift_snd _ _ _).symm
  base_naturality := by
    apply DividedPowerScheme.Hom.ext
    change t ≫ q ≫ C.toBase.hom = D.toBase.hom
    rw [← Category.assoc, ht]
    exact congrArg DividedPowerScheme.Hom.hom j.base_naturality
  toX_naturality := by
    change pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ C.toX = D.toX
    rw [← Category.assoc, pullback.lift_fst]
    exact j.toX_naturality

/-- A morphism of thickenings is determined by its ambient scheme map. -/
private theorem hom_ext_target {E F : GlobalCrystallineSituation.Thickening S}
    {a b : E ⟶ F} (h : a.targetHom.hom = b.targetHom.hom) : a = b := by
  apply GlobalCrystallineSituation.Thickening.Hom.ext
  · apply (cancel_mono F.thickening.immersion).mp
    rw [← a.immersion_naturality, ← b.immersion_naturality, h]
  · exact DividedPowerScheme.Hom.ext h

/-- A crystalline cone whose ambient square is cartesian computes a given
pullback once the canonical map into that cone preserves divided powers. -/
private theorem isPullback_target_of_cone
    (f : B ⟶ A) (g : C ⟶ A) (i : D ⟶ B) (j : D ⟶ C)
    (h : IsPullback i j f g)
    {E : GlobalCrystallineSituation.Thickening S} (a : E ⟶ B) (b : E ⟶ C)
    (hab : a ≫ f = b ≫ g)
    (hE : IsPullback a.targetHom.hom b.targetHom.hom
      f.targetHom.hom g.targetHom.hom)
    (l : D ⟶ E) (hl₁ : l ≫ a = i) (hl₂ : l ≫ b = j) :
    IsPullback i.targetHom.hom j.targetHom.hom
      f.targetHom.hom g.targetHom.hom := by
  let m : E ⟶ D := h.lift a b hab
  have hm₁ : m ≫ i = a := h.lift_fst a b hab
  have hm₂ : m ≫ j = b := h.lift_snd a b hab
  have hlm : l ≫ m = 𝟙 D := by
    apply h.hom_ext <;> simp [Category.assoc, hm₁, hm₂, hl₁, hl₂]
  have hml : m ≫ l = 𝟙 E := by
    apply hom_ext_target
    apply hE.hom_ext
    · simpa only [GlobalCrystallineSituation.Thickening.comp_targetHom,
        GlobalCrystallineSituation.Thickening.id_targetHom,
        DividedPowerScheme.Hom.comp_hom,
        DividedPowerScheme.Hom.id_hom] using
          congrArg (fun k : E ⟶ B => k.targetHom.hom)
            (show (m ≫ l) ≫ a = (𝟙 E) ≫ a by simp [Category.assoc, hl₁, hm₁])
    · simpa only [GlobalCrystallineSituation.Thickening.comp_targetHom,
        GlobalCrystallineSituation.Thickening.id_targetHom,
        DividedPowerScheme.Hom.comp_hom,
        DividedPowerScheme.Hom.id_hom] using
          congrArg (fun k : E ⟶ C => k.targetHom.hom)
            (show (m ≫ l) ≫ b = (𝟙 E) ≫ b by simp [Category.assoc, hl₂, hm₂])
  let e : D.thickening.target.scheme ≅ E.thickening.target.scheme :=
    { hom := l.targetHom.hom
      inv := m.targetHom.hom
      hom_inv_id := by
        simpa using congrArg (fun k : D ⟶ D => k.targetHom.hom) hlm
      inv_hom_id := by
        simpa using congrArg (fun k : E ⟶ E => k.targetHom.hom) hml }
  apply hE.of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa [e] using congrArg (fun k : D ⟶ B => k.targetHom.hom) hl₁
  · simpa [e] using congrArg (fun k : D ⟶ C => k.targetHom.hom) hl₂
  · simp
  · simp

/-- **Stacks Project, Tag 07IA.** Let a fibre square of divided power thickenings of `X`
relative to `(S, I, γ)` have vertices `(U₃, T₃, δ₃) ⟶ (U₂, T₂, δ₂)` and
`(U₁, T₁, δ₁) ⟶ (U, T, δ)`.  If `T₂ ⟶ T` is flat and `U₂ = T₂ ×_T U`, then `T₃ = T₁ ×_T T₂` as
schemes, with the projections of the original square.  Divided powers extend uniquely along a
flat ring map, so the ordinary fibre product of ambient schemes already carries the divided power
thickening computing the fibre product in `CRIS(X/S)`. -/
@[stacks 07IA]
theorem GlobalCrystallineSituation.Thickening.isPullback_targetHom_of_flat
    (f : B ⟶ A) (g : C ⟶ A) (i : D ⟶ B) (j : D ⟶ C)
    (h : IsPullback i j f g)
    (hf : Flat f.targetHom.hom)
    (hB : IsPullback B.thickening.immersion f.sourceHom
      f.targetHom.hom A.thickening.immersion) :
    IsPullback i.targetHom.hom j.targetHom.hom
      f.targetHom.hom g.targetHom.hom := by
  have : Flat f.targetHom.hom := hf
  let q := pullback.snd f.targetHom.hom g.targetHom.hom
  let E := flatBaseChangeCrystalline C q
  let b : E ⟶ C := flatBaseChangeCrystallineProjection C q
  have hb : b.targetHom.hom = q := rfl
  suffices hc : ∃ a : E ⟶ B,
      a.targetHom.hom = pullback.fst f.targetHom.hom g.targetHom.hom ∧
      ∃ l : D ⟶ E, l ≫ a = i ∧ l ≫ b = j by
    obtain ⟨a, ha, l, hl₁, hl₂⟩ := hc
    have hab : a ≫ f = b ≫ g := by
      apply hom_ext_target
      simp only [GlobalCrystallineSituation.Thickening.comp_targetHom,
        DividedPowerScheme.Hom.comp_hom]
      rw [ha, hb]
      exact pullback.condition
    apply isPullback_target_of_cone f g i j h a b hab _ l hl₁ hl₂
    rw [ha, hb]
    exact IsPullback.of_hasPullback _ _
  let p := pullback.fst f.targetHom.hom g.targetHom.hom
  have hpq : p ≫ f.targetHom.hom = q ≫ g.targetHom.hom := pullback.condition
  let aT : E.thickening.target ⟶ B.thickening.target :=
    { hom := p
      compatible := isDPMorphism_app_of_comp_cartesian A.thickening B.thickening
        f.targetHom f.sourceHom hB E.thickening.target p
        (b.targetHom ≫ g.targetHom) hpq }
  have hs : (E.thickening.immersion ≫ p) ≫ f.targetHom.hom =
      (b.sourceHom ≫ g.sourceHom) ≫ A.thickening.immersion :=
    calc (E.thickening.immersion ≫ p) ≫ f.targetHom.hom
        = E.thickening.immersion ≫ p ≫ f.targetHom.hom := Category.assoc _ _ _
      _ = E.thickening.immersion ≫ q ≫ g.targetHom.hom :=
          congrArg (fun z ↦ E.thickening.immersion ≫ z) hpq
      _ = (E.thickening.immersion ≫ q) ≫ g.targetHom.hom := (Category.assoc _ _ _).symm
      _ = (b.sourceHom ≫ g.sourceHom) ≫ A.thickening.immersion := by
          show (E.thickening.immersion ≫ b.targetHom.hom) ≫ g.targetHom.hom = _
          rw [b.immersion_naturality, Category.assoc, g.immersion_naturality,
            Category.assoc]
  let a : E ⟶ B :=
    { sourceHom := hB.lift (E.thickening.immersion ≫ p)
        (b.sourceHom ≫ g.sourceHom) hs
      targetHom := aT
      immersion_naturality := (hB.lift_fst _ _ hs).symm
      base_naturality := by
        apply DividedPowerScheme.Hom.ext
        show p ≫ B.toBase.hom = E.toBase.hom
        have hfbase := congrArg DividedPowerScheme.Hom.hom f.base_naturality
        have hgbase := congrArg DividedPowerScheme.Hom.hom g.base_naturality
        change f.targetHom.hom ≫ A.toBase.hom = B.toBase.hom at hfbase
        change g.targetHom.hom ≫ A.toBase.hom = C.toBase.hom at hgbase
        rw [← hfbase, ← Category.assoc, hpq, Category.assoc, hgbase]
        exact congrArg DividedPowerScheme.Hom.hom b.base_naturality
      toX_naturality := by
        rw [← f.toX_naturality, ← Category.assoc, hB.lift_snd,
          Category.assoc, g.toX_naturality]
        exact b.toX_naturality }
  have hw : i.targetHom.hom ≫ f.targetHom.hom =
      j.targetHom.hom ≫ g.targetHom.hom :=
    congrArg (fun k : D ⟶ A => k.targetHom.hom) h.w
  let t := pullback.lift i.targetHom.hom j.targetHom.hom hw
  let l : D ⟶ E := flatBaseChangeCrystallineLift C D q j t (pullback.lift_snd _ _ _)
  exact ⟨a, rfl, l, hom_ext_target (pullback.lift_fst _ _ _),
    hom_ext_target (pullback.lift_snd _ _ _)⟩

end Crystalline

end
