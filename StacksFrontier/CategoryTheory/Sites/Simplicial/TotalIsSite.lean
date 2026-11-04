module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Grothendieck
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CocontinuousTotalSite
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SimplexIso

/-!
# The total category of a simplicial family of sites is a site

The componentwise covering families of the Grothendieck construction of a simplicial family of
sites satisfy the three family-based site axioms, provided every transition functor is
cocontinuous and has representable pullbacks of covering families. The isomorphism axiom uses
that an isomorphism of the simplex category is an identity, so an isomorphism of the total
category lies in a single degree; the composition axiom is the composition axiom of one degree,
transported along the fibre inclusion; and the base-change axiom turns the representable
pullbacks of property P into genuine pullback squares of the total category.

## Main results

* `CategoryTheory.SimplicialCoverings.total_isSite`: the componentwise covering families make
  the Grothendieck construction of a simplicial family of sites into a site.

## Implementation notes

The pullback squares of the base-change axiom are produced by a helper stated in
`Grothendieck.mk` normal form, so that no object of the total category enters a goal as
`((Grothendieck.ι F m).obj p).base`: the transition between the two forms is definitional and is
made once, in `grothendieck_pullback_of_representable`, rather than inside every rewrite.

## References

* [Stacks Project, Tag 09WD](https://stacks.math.columbia.edu/tag/09WD)
* [Stacks Project, Tag 09W7](https://stacks.math.columbia.edu/tag/09W7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v a b w

namespace CategoryTheory

attribute [local implicit_reducible] CategoryTheory.Grothendieck.ι

namespace SimplicialCoverings

/-- A representable pullback in a fibre becomes a genuine pullback square in the Grothendieck
construction, with the arrows out of it given by the transition map and the fibre inclusion
written out in `Grothendieck.mk` form. -/
private lemma grothendieck_pullback_of_representable_mk
    {B : Type a} [Category.{b} B] {F : B ⥤ Cat.{v, u}}
    {m n : B} (d : m ⟶ n) {y : F.obj m} {t : F.obj n} (g : (F.map d).toFunctor.obj y ⟶ t)
    {x : F.obj n} (e : x ⟶ t) {p : F.obj m} (p₁ : p ⟶ y)
    (p₂ : (F.map d).toFunctor.obj p ⟶ x)
    (hpb : Functor.IsRepresentablePullback (F.map d).toFunctor g e p p₁ p₂) :
    IsPullback (C := Grothendieck F)
      (⟨d, p₂⟩ : (⟨m, p⟩ : Grothendieck F) ⟶ ⟨n, x⟩)
      (⟨𝟙 m, eqToHom (show (F.map (𝟙 m)).toFunctor.obj p = p by simp) ≫ p₁⟩ :
        (⟨m, p⟩ : Grothendieck F) ⟶ ⟨m, y⟩)
      (⟨𝟙 n, eqToHom (show (F.map (𝟙 n)).toFunctor.obj x = x by simp) ≫ e⟩ :
        (⟨n, x⟩ : Grothendieck F) ⟶ ⟨n, t⟩)
      (⟨d, g⟩ : (⟨m, y⟩ : Grothendieck F) ⟶ ⟨n, t⟩) := by
  have hfunm : (F.map (𝟙 m)).toFunctor = 𝟭 (F.obj m) :=
    congrArg Cat.Hom.toFunctor (F.map_id m)
  have hfunn : (F.map (𝟙 n)).toFunctor = 𝟭 (F.obj n) :=
    congrArg Cat.Hom.toFunctor (F.map_id n)
  apply IsPullback.mk'
  · refine Grothendieck.ext _ _ (by simp) ?_
    simp only [Grothendieck.comp_fiber, Functor.congr_hom hfunn p₂, eqToHom_map,
      eqToHom_trans_assoc, Category.assoc, Functor.id_map, eqToHom_refl, Category.id_comp,
      Functor.map_comp]
    rw [← hpb.1]
  · intro T φ φ' h₁ h₂
    obtain ⟨bb, f'⟩ := φ'
    have hbase : φ.base = bb := by simpa using congrArg Grothendieck.Hom.base h₂
    cases hbase
    have e₀ : (F.map (φ.base ≫ d)).toFunctor.obj T.fiber =
        (F.map d).toFunctor.obj ((F.map φ.base).toFunctor.obj T.fiber) := by simp
    have e₁ : (F.map (φ.base ≫ 𝟙 m)).toFunctor.obj T.fiber =
        (F.map (𝟙 m)).toFunctor.obj ((F.map φ.base).toFunctor.obj T.fiber) := by simp
    have hh₁ : (F.map d).toFunctor.map φ.fiber ≫ p₂ =
        (F.map d).toFunctor.map f' ≫ p₂ := by
      have hc := Grothendieck.congr h₁
      simp only [Grothendieck.comp_fiber, eqToHom_trans_assoc] at hc
      exact (cancel_epi (eqToHom e₀)).mp hc
    have hh₂ : φ.fiber ≫ p₁ = f' ≫ p₁ := by
      have hc := Grothendieck.congr h₂
      simp only [Grothendieck.comp_fiber, eqToHom_trans_assoc] at hc
      have hc' := (cancel_epi (eqToHom e₁)).mp hc
      have hmapφ := Functor.congr_hom hfunm φ.fiber
      have hmapf := Functor.congr_hom hfunm f'
      dsimp only at hc' hmapφ hmapf
      simp only [hmapφ, hmapf, Category.assoc, Functor.id_map, eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp] at hc'
      exact (cancel_epi (eqToHom (Functor.congr_obj hfunm
        ((F.map φ.base).toFunctor.obj T.fiber)))).mp hc'
    have hcond : (F.map d).toFunctor.map (φ.fiber ≫ p₁) ≫ g =
        ((F.map d).toFunctor.map φ.fiber ≫ p₂) ≫ e := by
      rw [Functor.map_comp, Category.assoc, hpb.1, Category.assoc]
    obtain ⟨l, -, huniq⟩ := hpb.2 ((F.map φ.base).toFunctor.obj T.fiber)
      (φ.fiber ≫ p₁) ((F.map d).toFunctor.map φ.fiber ≫ p₂) hcond
    exact Grothendieck.ext _ _ rfl (by
      simpa using (huniq φ.fiber ⟨rfl, rfl⟩).trans (huniq f' ⟨hh₂.symm, hh₁.symm⟩).symm)
  · intro T aa bb hab
    have hbase : aa.base = bb.base ≫ d := by
      simpa using congrArg Grothendieck.Hom.base hab
    obtain ⟨r, fa⟩ := aa
    obtain ⟨s, fb⟩ := bb
    dsimp only at hbase fa fb hab ⊢
    cases hbase
    have hobj : (F.map (s ≫ d)).toFunctor.obj T.fiber =
        (F.map d).toFunctor.obj ((F.map s).toFunctor.obj T.fiber) := by simp
    have hcondition : (F.map d).toFunctor.map fb ≫ g =
        (eqToHom hobj.symm ≫ fa) ≫ e := by
      have hc := Grothendieck.congr hab
      simp only [Grothendieck.comp_fiber, eqToHom_trans_assoc] at hc
      simp only [Functor.congr_hom hfunn fa, Category.assoc, Functor.id_map, eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp] at hc
      rw [eqToHom_comp_iff] at hc
      simp only [eqToHom_trans_assoc] at hc
      rw [Category.assoc, hc]
      simp
    obtain ⟨l, hl⟩ := hpb.2 ((F.map s).toFunctor.obj T.fiber) fb
      (eqToHom hobj.symm ≫ fa) hcondition
    refine ⟨⟨s, l⟩, ?_, ?_⟩
    · refine Grothendieck.ext _ _ rfl ?_
      simp only [Grothendieck.comp_fiber, eqToHom_trans_assoc]
      rw [hl.1.2]
      simp
    · refine Grothendieck.ext _ _ (by simp) ?_
      simp only [Grothendieck.comp_fiber, Functor.congr_hom hfunm l, Category.assoc,
        Functor.id_map, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [hl.1.1]

/-- A representable pullback in a fibre becomes a genuine pullback square in the Grothendieck
construction, with the two arrows out of it given by the transition map and the fibre
inclusion. -/
private lemma grothendieck_pullback_of_representable
    {B : Type a} [Category.{b} B] {F : B ⥤ Cat.{v, u}}
    {m n : B} (d : m ⟶ n) {y : F.obj m} {t : F.obj n} (g : (F.map d).toFunctor.obj y ⟶ t)
    {x : F.obj n} (e : x ⟶ t) {p : F.obj m} (p₁ : p ⟶ y)
    (p₂ : (F.map d).toFunctor.obj p ⟶ x)
    (hpb : Functor.IsRepresentablePullback (F.map d).toFunctor g e p p₁ p₂) :
    IsPullback
      (⟨d, p₂⟩ : (⟨m, p⟩ : Grothendieck F) ⟶ ⟨n, x⟩)
      ((Grothendieck.ι F m).map p₁)
      ((Grothendieck.ι F n).map e)
      (⟨d, g⟩ : (⟨m, y⟩ : Grothendieck F) ⟶ ⟨n, t⟩) :=
  grothendieck_pullback_of_representable_mk d g e p₁ p₂ hpb

/-- Pushing a family forward along the identity does nothing. -/
private lemma preZeroHypercover_pushforward_id {C : Type*} [Category C]
    {x : C} (E : PreZeroHypercover.{w} x) : E.pushforward (𝟙 x) = E := by
  cases E
  simp [PreZeroHypercover.pushforward]

/-- A componentwise covering family of the total category whose target lies in a given degree
comes from a covering family in that degree. -/
private lemma total_pushforward
    (F : SimplicialObject Cat.{v, u})
    (Cov : ∀ n, Covering.{u, v, max u v} (F.obj n) → Prop)
    (𝒱 : Covering.{u, v, max u v} (Grothendieck F))
    (h𝒱 : total F Cov 𝒱) {n : SimplexCategoryᵒᵖ} {x : F.obj n}
    (h : 𝒱.1 = (Grothendieck.ι F n).obj x) :
    ∃ E : PreZeroHypercover.{max u v} x,
      Cov n ⟨x, E⟩ ∧ 𝒱.2.pushforward (eqToHom h) = E.map (Grothendieck.ι F n) := by
  rcases 𝒱 with ⟨U, V⟩
  dsimp at h
  subst U
  obtain ⟨E, hE, hV⟩ := h𝒱
  refine ⟨E, hE, ?_⟩
  change V = E.map (Grothendieck.ι F n) at hV
  rwa [eqToHom_refl, preZeroHypercover_pushforward_id]

/-- Binding families commutes with pushing them forward along a functor. -/
private lemma preZeroHypercover_map_bind {C D : Type*} [Category C] [Category D]
    (G : C ⥤ D) {x : C} (E : PreZeroHypercover.{w} x)
    (V : ∀ i, PreZeroHypercover.{w} (E.X i)) :
    (E.map G).bind (fun i => (V i).map G) = (E.bind V).map G := by
  ext
  · rfl
  · rfl
  · exact heq_of_eq (funext fun _ => (G.map_comp _ _).symm)

/-- A morphism of the total category lying over the identity comes from a fibre morphism. -/
private lemma exists_map_ι_eq {B : Type a} [Category.{b} B] {F : B ⥤ Cat.{v, u}} {n : B}
    {a b : F.obj n} (h : (⟨n, a⟩ : Grothendieck F) ⟶ ⟨n, b⟩) (hb : h.base = 𝟙 n) :
    ∃ h₀ : a ⟶ b, (Grothendieck.ι F n).map h₀ = h := by
  refine ⟨eqToHom (by rw [hb]; simp) ≫ h.fiber, ?_⟩
  refine Grothendieck.ext _ _ (by simp [Grothendieck.ι, hb]) ?_
  dsimp [Grothendieck.ι]
  simp

/-- **Stacks 09WD.** If the transition functors in a simplicial family of sites are
cocontinuous and satisfy property P, then the componentwise covering families make its
Grothendieck construction into a site. -/
@[stacks 09WD, sga "4 VI 7.4.1" "simplicial, cocontinuous"]
theorem total_isSite (F : SimplicialObject Cat.{v, u})
    (Cov : ∀ n, Covering.{u, v, max u v} (F.obj n) → Prop)
    (hsite : ∀ n, IsSite (Cov n))
    (_hcocont : IsCocontinuous F Cov)
    (hP : ∀ {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n),
      Functor.HasCoverPullbacks (F.map f).toFunctor (Cov m) (Cov n)) :
    IsSite (total F Cov) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro U V f hf
    let fi : U ⟶ V := inv f
    cases U with
    | mk n x =>
    cases V with
    | mk m y =>
    have hinv : f ≫ fi = 𝟙 _ := IsIso.hom_inv_id f
    have : IsIso f.base := (inferInstance : IsIso ((Grothendieck.forget F).map f))
    obtain ⟨hUV, _⟩ := SimplexCategory.exists_eq_eqToHom_of_isIso f.base
    cases hUV
    have hbase : f.base = 𝟙 n := by
      simpa using congrArg Quiver.Hom.op (SimplexCategory.eq_id_of_isIso f.base.unop)
    have hfi : fi.base = 𝟙 n := by
      have h := congrArg Grothendieck.Hom.base hinv
      rw [Grothendieck.comp_base, Grothendieck.id_base, hbase] at h
      simpa using h
    obtain ⟨f₀, hfmap⟩ := exists_map_ι_eq f hbase
    obtain ⟨fi₀, hfimap⟩ := exists_map_ι_eq fi hfi
    have hfiber₁ : f₀ ≫ fi₀ = 𝟙 y := by
      apply (Grothendieck.ι F n).map_injective
      rwa [Functor.map_comp, hfmap, hfimap, (Grothendieck.ι F n).map_id]
    have hfiber₂ : fi₀ ≫ f₀ = 𝟙 x := by
      apply (Grothendieck.ι F n).map_injective
      rw [Functor.map_comp, hfimap, hfmap, (Grothendieck.ι F n).map_id]
      exact IsIso.inv_hom_id f
    have : IsIso f₀ := ⟨⟨fi₀, hfiber₁, hfiber₂⟩⟩
    rcases hsite n with ⟨hiso, _, _⟩
    change total F Cov ⟨⟨n, x⟩, PreZeroHypercover.singleton f⟩
    refine ⟨PreZeroHypercover.singleton f₀, hiso f₀, ?_⟩
    ext
    · rfl
    · rfl
    · apply heq_of_eq
      funext i
      cases i
      simpa [PreZeroHypercover.singleton, PreZeroHypercover.map, Grothendieck.ι] using
        hfmap.symm
  · intro 𝒰 h𝒰
    rcases 𝒰 with ⟨⟨n, t⟩, EU⟩
    change ∃ E : PreZeroHypercover.{max u v} t,
      Cov n ⟨t, E⟩ ∧ EU = E.map (Grothendieck.ι F n) at h𝒰
    obtain ⟨E, hE, rfl⟩ := h𝒰
    intro 𝒱 h𝒱 htargets
    choose V hV heq using fun i =>
      total_pushforward F Cov (𝒱 i) (h𝒱 i) (htargets i)
    refine ⟨E.bind V, ?_, ?_⟩
    · simpa only [eqToHom_refl, preZeroHypercover_pushforward_id] using
        (hsite n).2.1 ⟨t, E⟩ hE (fun i => ⟨E.X i, V i⟩) hV (fun _ => rfl)
    · change (E.map (Grothendieck.ι F n)).bind _ = _
      exact (congrArg (E.map (Grothendieck.ι F n)).bind (funext heq)).trans
        (preZeroHypercover_map_bind _ _ _)
  · intro 𝒰 h𝒰 V g
    rcases 𝒰 with ⟨⟨n, t⟩, EU⟩
    obtain ⟨E, hE, hEU⟩ := h𝒰
    change EU = E.map (Grothendieck.ι F n) at hEU
    rw [hEU]
    obtain ⟨m, x⟩ := V
    obtain ⟨d, gf⟩ := g
    obtain ⟨P, p₁, p₂, hpb, hCov⟩ := hP d ⟨t, E⟩ hE x gf
    exact ⟨fun i => ⟨m, P i⟩, fun i => ⟨d, p₂ i⟩, fun i => (Grothendieck.ι F m).map (p₁ i),
      fun i => grothendieck_pullback_of_representable d gf (E.f i) (p₁ i) (p₂ i) (hpb i),
      ⟨E.I₀, P, p₁⟩, hCov, rfl⟩

end SimplicialCoverings

end CategoryTheory

end
