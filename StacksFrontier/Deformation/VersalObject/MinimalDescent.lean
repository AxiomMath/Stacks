module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.BaseCategory.FibreProduct
public import StacksFrontier.Deformation.BaseCategory.IdealQuotient
public import StacksFrontier.Deformation.Schlessinger.Basic
public import StacksFrontier.Deformation.SchlessingerConditions.CofiberedLifts
public import StacksFrontier.Deformation.VersalObject.Descent

/-!
# Minimality of descent objects under pushforward

Let `p : F ⥤ 𝒞_Λ` be cofibered in groupoids and satisfy Schlessinger's condition (S1). Two
facts about the descent categories of Stacks 90.14 and the pushforward functor between them:

* pushing a minimal descent object forward along any morphism again gives a minimal descent
  object, and
* when the morphism lies over a surjection, every minimal descent object of the target is, up
  to isomorphism, the pushforward of a minimal descent object of the source.

Both proofs are the ones in the source. For the first, a morphism into the pushforward is
completed, using (S1) over the fibre product of the two base subalgebras, to a morphism into
the original object; minimality of the original makes that an isomorphism, and the comparison
arrows are cocartesian, so the morphism one started from is an isomorphism too. For the
second, (S1) over the fibre product of the base subalgebra of the target with the base map
produces a descent object of the source whose pushforward maps to the target; one then passes
to a minimal descent object below it, which exists because the length of `p(y)` over `Λ` is
finite, and minimality of the target makes the resulting map an isomorphism.

## Main results

* `Deformation.isMinimal_descentPushforward`: pushforward preserves minimality.
* `Deformation.exists_minimal_preimage`: minimal descent objects lift across a surjection.

## Implementation notes

The image is represented by the specified `Deformation.descentPushforward`; its agreement with
the target is expressed by an isomorphism in the descent category, so it does not depend on a
choice of representative for the image subalgebra.

For `exists_minimal_preimage` the chapter's standing assumptions that `Λ` is Noetherian and
`k` is finite over `Λ` are carried as instance arguments: they are what makes the `Λ`-length of
an object of `𝒞_Λ` finite, and that finiteness is what lets one choose a minimal descent
object below a given one.

## References

* [Stacks Project, Tag 06T1](https://stacks.math.columbia.edu/tag/06T1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w u₁ v₁ uF vF

namespace Deformation

private theorem injective_hom_of_isIso
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A B : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : A ⟶ B) [IsIso f] :
  Function.Injective f.hom := by
  intro a b hab
  have h' := congrArg (inv f).hom hab
  simpa only [← AlgHom.comp_apply, ← ArtinianLocalAlgCat.comp_hom,
    IsIso.hom_inv_id, ArtinianLocalAlgCat.id_hom, AlgHom.id_apply] using h'

private def baseLinearMap
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A B : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : A ⟶ B) :
    letI : Module Λ A := Module.compHom A (algebraMap Λ A)
    letI : Module Λ B := Module.compHom B (algebraMap Λ B)
    A →ₗ[Λ] B := by
  letI : Module Λ A := Module.compHom A (algebraMap Λ A)
  letI : Module Λ B := Module.compHom B (algebraMap Λ B)
  exact
    { toFun := f.hom
      map_add' := f.hom.map_add
      map_smul' := by
        intro r a
        change f.hom (algebraMap Λ A r * a) = algebraMap Λ B r * f.hom a
        rw [map_mul, f.hom.commutes] }

private theorem finite_length_base
    {Λ : Type u} {k : Type w} [CommRing Λ] [IsNoetherianRing Λ]
    [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k) :
    letI : Module Λ A := Module.compHom A (algebraMap Λ A)
    Module.length Λ A ≠ ⊤ := by
  let : Module Λ A := Module.compHom A (algebraMap Λ A)
  have hlen := finrank_residueImageField_mul_length_eq_length Λ k A A
    A.residueEquiv
  change Module.length Λ A ≠ ⊤
  rw [← hlen]
  exact WithTop.mul_ne_top (ENat.natCast_ne_top _) Module.length_ne_top

/-- A morphism of descent objects whose underlying arrow is an isomorphism is an isomorphism. -/
private theorem isIso_of_isIso_hom_left
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k} {y : F} {Z X : DescentObject p y}
    (m : Z ⟶ X) [IsIso m.hom.left] : IsIso m := by
  have : IsIso ((Over.forget y).map m.hom) := ‹_›
  have : IsIso m.hom := isIso_of_reflects_iso m.hom (Over.forget y)
  exact (ObjectProperty.isIso_hom_iff m).mp inferInstance

/-- The comparison arrow into a descent pushforward is surjective on base algebras. -/
private theorem surjective_map_inclusion
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k} {y x : F} {g : y ⟶ x}
    (D : DescentPushforward p g) (X : DescentObject p y) :
    Function.Surjective (p.map (D.inclusion X)).hom := by
  intro b
  obtain ⟨a, ha⟩ : (p.map (D.functor.obj X).obj.hom).hom b ∈
      AlgHom.range (p.map (X.obj.hom ≫ g)).hom := by
    rw [← D.base_range X]
    exact AlgHom.mem_range_self _ b
  have hc : p.map (D.inclusion X) ≫ p.map (D.functor.obj X).obj.hom =
      p.map (X.obj.hom ≫ g) := by
    rw [← p.map_comp, D.inclusion_fac]
  exact ⟨a, (D.functor.obj X).property ((congrArg (·.hom a) hc).trans ha)⟩

private theorem exists_minimal_below
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) {y : F}
    (hB : letI : Module Λ (p.obj y) :=
      Module.compHom (p.obj y) (algebraMap Λ (p.obj y))
      Module.length Λ (p.obj y) ≠ ⊤)
    (Z : DescentObject p y) :
    ∃ (Y : DescentObject p y) (_f : Y ⟶ Z), IsMinimalObject Y := by
  classical
  let : Module Λ (p.obj y) :=
    Module.compHom (p.obj y) (algebraMap Λ (p.obj y))
  let measure (Q : DescentObject p y) : ℕ :=
    (let : Module Λ (p.obj Q.obj.left) :=
      Module.compHom (p.obj Q.obj.left) (algebraMap Λ (p.obj Q.obj.left))
     (Module.length Λ (p.obj Q.obj.left)).toNat)
  let P : ℕ → Prop := fun n => ∃ (Q : DescentObject p y) (f : Q ⟶ Z), measure Q = n
  have hP : ∃ n, P n := ⟨measure Z, Z, 𝟙 Z, rfl⟩
  let n := Nat.find hP
  obtain ⟨Y, q, hmeasureY⟩ := Nat.find_spec hP
  refine ⟨Y, q, ?_⟩
  intro W f
  let : Module Λ (p.obj W.obj.left) :=
    Module.compHom (p.obj W.obj.left) (algebraMap Λ (p.obj W.obj.left))
  let : Module Λ (p.obj Y.obj.left) :=
    Module.compHom (p.obj Y.obj.left) (algebraMap Λ (p.obj Y.obj.left))
  let ψ : p.obj W.obj.left →ₗ[Λ] p.obj Y.obj.left :=
    baseLinearMap (p.map f.hom.left)
  have hψ : Function.Injective ψ := by
    intro a b hab
    change (p.map f.hom.left).hom a = (p.map f.hom.left).hom b at hab
    apply W.property
    have h := congrArg ArtinianLocalAlgCat.Hom.hom
      ((p.map_comp _ _).symm.trans (congrArg p.map f.hom.w))
    exact (DFunLike.congr_fun h a).symm.trans
      ((congrArg (p.map Y.obj.hom).hom hab).trans (DFunLike.congr_fun h b))
  have hlenle : Module.length Λ (p.obj W.obj.left) ≤ Module.length Λ (p.obj Y.obj.left) :=
    Module.length_le_of_injective ψ hψ
  have hlenY : Module.length Λ (p.obj Y.obj.left) ≠ ⊤ := ne_top_of_le_ne_top hB
    (Module.length_le_of_injective (baseLinearMap (p.map Y.obj.hom)) Y.property)
  have hlenW : Module.length Λ (p.obj W.obj.left) ≠ ⊤ := ne_top_of_le_ne_top hlenY hlenle
  have hNatLe : measure W ≤ measure Y := ENat.toNat_le_toNat hlenle hlenY
  have hNatMin : n ≤ measure W := Nat.find_min' hP ⟨W, f ≫ q, rfl⟩
  have hNatEq : measure W = measure Y := by
    have hmy : measure Y = n := by simpa [n] using hmeasureY
    omega
  change (Module.length Λ (p.obj W.obj.left)).toNat =
    (Module.length Λ (p.obj Y.obj.left)).toNat at hNatEq
  have hlenEq : Module.length Λ (p.obj W.obj.left) = Module.length Λ (p.obj Y.obj.left) := by
    rw [← ENat.natCast_toNat hlenW, ← ENat.natCast_toNat hlenY, hNatEq]
  have hsurj : Function.Surjective ψ := by
    by_contra hnot
    have hfinite : IsFiniteLength Λ (p.obj Y.obj.left) := Module.length_ne_top_iff.mp hlenY
    have hprops := isFiniteLength_iff_isNoetherian_isArtinian.mp hfinite
    let : IsNoetherian Λ (p.obj Y.obj.left) := hprops.1
    let : IsArtinian Λ (p.obj Y.obj.left) := hprops.2
    have hproper : LinearMap.range ψ ≠ ⊤ := fun heq ↦ hnot (LinearMap.range_eq_top.mp heq)
    have hlt := Submodule.length_lt (R := Λ) (M := p.obj Y.obj.left) hproper
    rw [← (LinearEquiv.ofBijective ψ.rangeRestrict
      ⟨fun a b hab => hψ (Subtype.ext_iff.mp hab),
        LinearMap.surjective_rangeRestrict ψ⟩).length_eq] at hlt
    exact (not_lt_of_ge (le_of_eq hlenEq.symm)) hlt
  let : IsIso (p.map f.hom.left) := ArtinianLocalAlgCat.isIso_of_bijective_hom _ ⟨hψ, hsurj⟩
  have : IsIso f.hom.left := isIso_of_isIso_map hp f.hom.left
  exact isIso_of_isIso_hom_left f

/-- Every minimal descent object of `x` is, up to isomorphism, the image of a
minimal descent object of `y` when `y ⟶ x` lies over a surjection and (S1)
holds. -/
@[stacks 06T1 "minimality_lifted"]
theorem exists_minimal_preimage
    {Λ : Type u} {k : Type w} [CommRing Λ] [IsNoetherianRing Λ]
    [Field k] [Algebra Λ k] [Module.Finite Λ k]
    {F : Type u₁} [Category.{v₁} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    {y x : F} (g : y ⟶ x)
    (hg : Function.Surjective (p.map g).hom)
    (X : DescentObject p x) (hX : IsMinimalObject X) :
    ∃ Y : DescentObject p y,
      IsMinimalObject Y ∧ Nonempty ((descentPushforward p hp g).functor.obj Y ≅ X) := by
  classical
  let f₁ := p.map X.obj.hom
  let f₂ := p.map g
  let P := ArtinianLocalAlgCat.pullbackObj_of_surjective
    f₁ f₂ (Or.inr hg)
  let q₁ := ArtinianLocalAlgCat.pullbackFst_of_surjective
    f₁ f₂ (Or.inr hg)
  let q₂ := ArtinianLocalAlgCat.pullbackSnd_of_surjective
    f₁ f₂ (Or.inr hg)
  obtain ⟨C⟩ := hS1.completion X.obj.hom g hg q₁ q₂
    (ArtinianLocalAlgCat.isPullback_of_surjective
      f₁ f₂ (Or.inr hg)).flip
  have hq₂ : Function.Injective q₂.hom := by
    intro a b hab
    rw [ArtinianLocalAlgCat.pullbackSnd_of_surjective_hom] at hab
    have hab' : a.1.2 = b.1.2 := hab
    refine Subtype.ext (Prod.ext (X.property ?_) hab')
    calc
      f₁.hom a.1.1 = f₂.hom a.1.2 := a.2
      _ = f₂.hom b.1.2 := congrArg f₂.hom hab'
      _ = f₁.hom b.1.1 := b.2.symm
  have htoSecond : Function.Injective (p.map C.toSecond).hom := by
    have hcomp : (p.map C.toSecond).hom =
        q₂.hom.comp (eqToHom C.apex_eq).hom := by
      simpa only [ArtinianLocalAlgCat.comp_hom] using
        congrArg ArtinianLocalAlgCat.Hom.hom C.map_toSecond
    rw [hcomp]
    exact hq₂.comp (injective_hom_of_isIso (eqToHom C.apex_eq))
  let Z : DescentObject p y := ⟨Over.mk C.toSecond, htoSecond⟩
  let D := descentPushforward p hp g
  let Z₁ := D.functor.obj Z
  let i := D.inclusion Z
  have hfac : p.map (Z.obj.hom ≫ g) = p.map C.toFirst ≫ p.map X.obj.hom :=
    (congrArg p.map C.comm).trans (p.map_comp _ _)
  have hbase_range : AlgHom.range (p.map Z₁.obj.hom).hom ≤
      AlgHom.range (p.map X.obj.hom).hom := by
    rw [D.base_range Z, hfac]
    simpa only [ArtinianLocalAlgCat.comp_hom] using
      (AlgHom.range_comp_le_range (p.map C.toFirst).hom (p.map X.obj.hom).hom)
  obtain ⟨rbase, hrbase⟩ := ArtinianLocalAlgCat.exists_factor_of_range_le
    (p.map Z₁.obj.hom) (p.map X.obj.hom)
    X.property hbase_range
  let : Mono (p.map X.obj.hom) :=
    ArtinianLocalAlgCat.mono_of_injective (p.map X.obj.hom) X.property
  have hbase : p.map i ≫ rbase = p.map C.toFirst := by
    apply (cancel_mono (p.map X.obj.hom)).1
    calc
      (p.map i ≫ rbase) ≫ p.map X.obj.hom =
          p.map i ≫ (rbase ≫ p.map X.obj.hom) := by simp [Category.assoc]
      _ = p.map i ≫ p.map Z₁.obj.hom := by rw [hrbase]
      _ = p.map (Z.obj.hom ≫ g) := by rw [← p.map_comp, D.inclusion_fac Z]
      _ = p.map C.toFirst ≫ p.map X.obj.hom := hfac
  obtain ⟨s, hs, _⟩ := existsUnique_factor_of_isHomLift hp i C.toFirst rbase hbase
  let : Epi (p.map i) :=
    ArtinianLocalAlgCat.epi_of_surjective (p.map i) (surjective_map_inclusion D Z)
  have : Epi i := epi_of_epi_map p hp i
  have hs_over : s ≫ X.obj.hom = Z₁.obj.hom := by
    apply (cancel_epi i).1
    calc
      i ≫ (s ≫ X.obj.hom) = (i ≫ s) ≫ X.obj.hom := by simp [Category.assoc]
      _ = C.toFirst ≫ X.obj.hom := by rw [hs.2]
      _ = Z.obj.hom ≫ g := C.comm.symm
      _ = i ≫ Z₁.obj.hom := (D.inclusion_fac Z).symm
  let r : Z₁ ⟶ X := ObjectProperty.homMk (Over.homMk s hs_over)
  let : Module Λ (p.obj y) := Module.compHom (p.obj y) (algebraMap Λ (p.obj y))
  obtain ⟨Y, t, hY⟩ := exists_minimal_below p hp
    (finite_length_base (Λ := Λ) (k := k) (p.obj y)) Z
  let m : (D.functor.obj Y) ⟶ X := (D.functor.map t) ≫ r
  have : IsIso m := hX (D.functor.obj Y) m
  exact ⟨Y, hY, ⟨asIso m⟩⟩

/-- Pushforward along a morphism preserves minimal descent objects under (S1). -/
@[stacks 06T1 "minimality_preserved"]
theorem isMinimal_descentPushforward
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    {y x : F} (g : y ⟶ x)
    (X : DescentObject p y)
    (hX : IsMinimalObject X) :
    IsMinimalObject
      ((descentPushforward p hp g).functor.obj X) := by
  let D := descentPushforward p hp g
  let X' := D.functor.obj X
  intro Z m
  let y' := X.obj.left
  let x' := X'.obj.left
  let B := p.obj y'
  let j : y' ⟶ x' := D.inclusion X
  let α : Z.obj.left ⟶ x' := m.hom.left
  let q : B ⟶ p.obj x' := p.map j
  let r : p.obj Z.obj.left ⟶ p.obj x' := p.map α
  let t : p.obj x' ⟶ p.obj x := p.map X'.obj.hom
  have hq : Function.Surjective q.hom := surjective_map_inclusion D X
  have hr : Function.Injective r.hom := by
    have hcomp : r ≫ t = p.map Z.obj.hom := by
      change p.map α ≫ p.map X'.obj.hom = _
      rw [← p.map_comp, m.hom.w]
    exact fun a b hab ↦ Z.property (by rw [← hcomp]; exact congrArg t.hom hab)
  let P := ArtinianLocalAlgCat.pullbackObj_of_surjective
    q r (Or.inl hq)
  let u := ArtinianLocalAlgCat.pullbackFst_of_surjective
    q r (Or.inl hq)
  let v := ArtinianLocalAlgCat.pullbackSnd_of_surjective
    q r (Or.inl hq)
  have hpb' : IsPullback u v q r :=
    ArtinianLocalAlgCat.isPullback_of_surjective q r (Or.inl hq)
  have hcompl : Nonempty (PullbackCompletion p α j v u) :=
    hS1.completion α j hq v u hpb'
  let W := Classical.choice hcompl
  let Y : DescentObject p y :=
    ⟨Over.mk (W.toSecond ≫ X.obj.hom), by
      have hu_inj : Function.Injective u.hom := by
        intro z z' hzz
        have hfirst : z.1.1 = z'.1.1 := by
          have hfst := hzz
          rw [ArtinianLocalAlgCat.pullbackFst_of_surjective_hom]
            at hfst
          change (AlgHom.fst Λ B (p.obj Z.obj.left)
              ((q.hom.pullback r.hom).val z)) =
            (AlgHom.fst Λ B (p.obj Z.obj.left)
              ((q.hom.pullback r.hom).val z')) at hfst
          simpa only [AlgHom.fst_apply, Subalgebra.coe_val] using hfst
        refine Subtype.ext (Prod.ext hfirst (hr ?_))
        have hz : q.hom z.1.1 = r.hom z.1.2 := by
          simpa [AlgHom.pullback] using z.2
        have hz' : q.hom z'.1.1 = r.hom z'.1.2 := by
          simpa [AlgHom.pullback] using z'.2
        calc
          r.hom z.1.2 = q.hom z.1.1 := hz.symm
          _ = q.hom z'.1.1 := congrArg q.hom hfirst
          _ = r.hom z'.1.2 := hz'
      have hcast : Function.Injective (eqToHom W.apex_eq).hom :=
        injective_hom_of_isIso (eqToHom W.apex_eq)
      have hbase : Function.Injective (p.map (W.toSecond ≫ X.obj.hom)).hom := by
        intro a b hab
        have hcomp : (p.map X.obj.hom).hom
            (u.hom ((eqToHom W.apex_eq).hom a)) = (p.map X.obj.hom).hom
            (u.hom ((eqToHom W.apex_eq).hom b)) := by
          simpa [Functor.map_comp, ArtinianLocalAlgCat.comp_hom,
            AlgHom.comp_apply, W.map_toSecond] using hab
        exact hcast (hu_inj (X.property hcomp))
      exact hbase⟩
  let n : Y ⟶ X := ⟨Over.homMk W.toSecond (by simp [Y])⟩
  have hn : IsIso n := hX Y n
  have hnOver : IsIso n.hom := (ObjectProperty.isIso_hom_iff n).mpr hn
  have : IsIso u := by
    have : IsIso W.toSecond := by
      have hforget : IsIso ((Over.forget y).map n.hom) :=
        (isIso_iff_of_reflects_iso n.hom (Over.forget y)).mpr hnOver
      simpa [n] using hforget
    have : IsIso (eqToHom W.apex_eq ≫ u) := by
      simpa [W.map_toSecond] using Functor.map_isIso p W.toSecond
    exact IsIso.of_isIso_comp_left (eqToHom W.apex_eq) u
  have hu_surj : Function.Surjective u.hom := by
    intro b
    refine ⟨(inv u).hom b, ?_⟩
    have h := congrArg (fun f : B ⟶ B => f.hom b) (IsIso.inv_hom_id u)
    simpa only [ArtinianLocalAlgCat.comp_hom, ArtinianLocalAlgCat.id_hom,
      AlgHom.comp_apply, AlgHom.id_apply] using h
  have hr_surj : Function.Surjective r.hom := by
    intro a
    obtain ⟨b, hb⟩ := hq a
    obtain ⟨z, hz⟩ := hu_surj b
    refine ⟨v.hom z, ?_⟩
    have hcomm := congrArg (fun f : P ⟶ p.obj x' => f.hom z) hpb'.w
    have hcomm' : q.hom (u.hom z) = r.hom (v.hom z) := by
      simpa [ArtinianLocalAlgCat.comp_hom, AlgHom.comp_apply] using hcomm
    rw [← hcomm', hz, hb]
  have : p.IsStronglyCocartesian r α :=
    isStronglyCocartesian_of_isCofiberedInGroupoids hp r α inferInstance
  have : IsIso r := ArtinianLocalAlgCat.isIso_of_bijective_hom r ⟨hr, hr_surj⟩
  have hα : IsIso α := Functor.IsStronglyCocartesian.isIso_of_base_isIso p r α
  have : IsIso m.hom.left := hα
  exact isIso_of_isIso_hom_left m

end Deformation

end
