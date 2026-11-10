module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.StackOfTorsors.FiberedInGroupoids
import StacksCore.Tactic.StacksAttribute

/-!
# The Isom presheaves of the stack of torsors are sheaves

Condition (2) of Stacks 02ZI for the functor `p : 𝒢-Torsors ⥤ C` of Stacks 04UJ
(`SheafOfGroups.Torsors.projection_isomIsSheaf`, Stacks 04UK), together with
`SheafOfGroups.Torsors.isEffective_of_glueing`, which reduces the effectivity of a descent
datum to a glueing of its objects.
-/

@[expose] public section

open CategoryTheory Opposite

universe t w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace SheafOfGroups.Torsors

variable {𝒢 : SheafOfGroups.{w} (C := C) J}

universe s

/-- **Stacks 04UK**, condition (2) of Stacks 02ZI: the presheaves `Isom(x, y)` on `C/U` are
sheaves. For two torsors `x` and `y` over the same object `U` of `C` and a covering family
`{V i → U}` of `U` whose overlaps are genuine fibre products `V i ×_U V j`, a family of
isomorphisms `x|_{V i} ⟶ y|_{V i}` of torsors which agree on the overlaps glues to a unique
isomorphism `x ⟶ y` of `𝒢|_U`-torsors restricting to the given ones.

The glued morphism is produced by the sheaf condition for the torsor `y` on `C/U`: a section of
`x` over an object of `C/U` is, locally on a covering refining `{V i → U}`, the image of a
section of a restriction `x|_{V i}` under the cartesian morphism `x|_{V i} ⟶ x`, and applying
the given isomorphism there prescribes the sought section of `y` locally. The prescriptions
agree because two local factorizations through `f i` and `f j` factor jointly through the fibre
product `V i ×_U V j`, where the hypothesis supplies a single common restriction of the two
isomorphisms. Equivariance for `𝒢` and compatibility with the restriction maps are inherited
pointwise from the given isomorphisms, and the glued morphism is an isomorphism because a
morphism of `𝒢-Torsors` lying over an isomorphism of `C` is one (Stacks 04UJ). -/
@[stacks 04UK "condition (2): the Isom presheaves are sheaves"]
theorem projection_isomIsSheaf {U : C} (x y : Torsors.{t} 𝒢)
    (hx : projection.obj x = U) (hy : projection.obj y = U)
    {I : Type s} (V : I → C) (f : ∀ i, V i ⟶ U) (hf : Sieve.ofArrows V f ∈ J U)
    (Vij : I → I → C) (pr₁ : ∀ i j, Vij i j ⟶ V i) (pr₂ : ∀ i j, Vij i j ⟶ V j)
    (hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j))
    (xr : ∀ i, Functor.Restriction projection (f i) x hx)
    (yr : ∀ i, Functor.Restriction projection (f i) y hy)
    (xrij : ∀ i j, Functor.Restriction projection (pr₁ i j ≫ f i) x hx)
    (yrij : ∀ i j, Functor.Restriction projection (pr₁ i j ≫ f i) y hy) :
    Functor.IsomIsSheafFor projection x y hx hy V f Vij pr₁ pr₂ hVij xr yr xrij yrij := by
  intro φ hφ _ hcompat
  have hxb : x.base = U := hx
  have hyb : y.base = U := hy
  have hxp : ∀ i, (xr i).pt.base = V i := fun i => (xr i).hpt
  have hyp : ∀ i, (yr i).pt.base = V i := fun i => (yr i).hpt
  have hax : ∀ i, Hom.base (xr i).hom = eqToHom (hxp i) ≫ f i ≫ eqToHom hxb.symm :=
    fun i => base_eq_of_isHomLift _ (xr i).isHomLift
  have hay : ∀ i, Hom.base (yr i).hom = eqToHom (hyp i) ≫ f i ≫ eqToHom hyb.symm :=
    fun i => base_eq_of_isHomLift _ (yr i).isHomLift
  have hbi : ∀ i, Hom.base (φ i) = eqToHom (hxp i) ≫ eqToHom (hyp i).symm :=
    fun i => base_eq_of_isHomLift _ (hφ i)
  have hΦ : ∀ i, Hom.base (φ i ≫ (yr i).hom) =
      Hom.base (xr i).hom ≫ (eqToHom hxb ≫ eqToHom hyb.symm) := by
    intro i
    change Hom.base (φ i) ≫ Hom.base (yr i).hom = _
    rw [hbi, hay, hax]
    simp
  have hSiff : ∀ {W : C} (a : W ⟶ x.base),
      ((Sieve.ofArrows V f).pullback (eqToHom hxb)).arrows a ↔
        ∃ (i : I) (c : W ⟶ V i), a = c ≫ f i ≫ eqToHom hxb.symm := by
    intro W a
    change (Sieve.ofArrows V f).arrows (a ≫ eqToHom hxb) ↔ _
    rw [Sieve.mem_ofArrows_iff]
    constructor
    · rintro ⟨i, c, hc⟩
      refine ⟨i, c, ?_⟩
      rw [← Category.assoc, ← hc]
      simp
    · rintro ⟨i, c, hc⟩
      refine ⟨i, c, ?_⟩
      rw [hc]
      simp
  have hS : (Sieve.ofArrows V f).pullback (eqToHom hxb) ∈ J x.base := J.pullback_stable _ hf
  have hlift : ∀ (i : I) {W : Cᵒᵖ} (p : x.Total W) (c : W.unop ⟶ V i),
      p.1 = c ≫ f i ≫ eqToHom hxb.symm →
      ∃! p' : (xr i).pt.Total W,
        p'.1 = c ≫ eqToHom (hxp i).symm ∧ (xr i).hom.map W p' = p := by
    intro i W p c hc
    refine (xr i).hom.existsUnique_map (c ≫ eqToHom (hxp i).symm) p ?_
    rw [hc, hax i]
    simp
  have hagree : ∀ {W : Cᵒᵖ} (i j : I) (p : x.Total W) (c : W.unop ⟶ V i) (d : W.unop ⟶ V j),
      p.1 = c ≫ f i ≫ eqToHom hxb.symm → p.1 = d ≫ f j ≫ eqToHom hxb.symm →
      ∀ (pi : (xr i).pt.Total W) (pj : (xr j).pt.Total W),
      pi.1 = c ≫ eqToHom (hxp i).symm → (xr i).hom.map W pi = p →
      pj.1 = d ≫ eqToHom (hxp j).symm → (xr j).hom.map W pj = p →
      (φ i ≫ (yr i).hom).map W pi = (φ j ≫ (yr j).hom).map W pj := by
    intro W i j p c d hc hd pi pj hpi hpi' hpj hpj'
    obtain ⟨γ, -, hγ₁, hγ₂⟩ := hcompat i j
    have hcd : c ≫ f i = d ≫ f j := by
      simpa using congrArg (fun z => z ≫ eqToHom hxb) (hc.symm.trans hd)
    obtain ⟨ee, he₁, he₂⟩ : ∃ ee : W.unop ⟶ Vij i j, ee ≫ pr₁ i j = c ∧ ee ≫ pr₂ i j = d :=
      ⟨(hVij i j).lift c d hcd, (hVij i j).lift_fst c d hcd, (hVij i j).lift_snd c d hcd⟩
    have hstar : Functor.Restriction.compTo projection (pr₁ i j) (f i) rfl (xr i) (xrij i j) ≫
          (φ i ≫ (yr i).hom) =
        Functor.Restriction.compTo projection (pr₂ i j) (f j) (hVij i j).w (xr j) (xrij i j) ≫
          (φ j ≫ (yr j).hom) := by
      rw [← Category.assoc, ← Category.assoc, ← hγ₁, ← hγ₂, Category.assoc, Category.assoc,
        Functor.Restriction.compTo_hom, Functor.Restriction.compTo_hom]
    have hRp : (xrij i j).pt.base = Vij i j := (xrij i j).hpt
    have hRbase : Hom.base (xrij i j).hom =
        eqToHom hRp ≫ (pr₁ i j ≫ f i) ≫ eqToHom hxb.symm :=
      base_eq_of_isHomLift _ (xrij i j).isHomLift
    obtain ⟨r, ⟨hr₁, hr₂⟩, -⟩ := (xrij i j).hom.existsUnique_map
      (ee ≫ eqToHom hRp.symm) p (by
        rw [hc, hRbase, ← he₁]
        simp)
    have hcomp : ∀ (k : I) (g : Vij i j ⟶ V k) (hg : pr₁ i j ≫ f i = g ≫ f k) (z : W.unop ⟶ V k),
        ee ≫ g = z → p.1 = z ≫ f k ≫ eqToHom hxb.symm → ∀ pk : (xr k).pt.Total W,
        pk.1 = z ≫ eqToHom (hxp k).symm → (xr k).hom.map W pk = p →
        Hom.map (Functor.Restriction.compTo projection g (f k) hg (xr k) (xrij i j)) W r = pk := by
      rintro k g hg _ rfl hzp pk hpk hpk'
      refine (hlift k p _ hzp).unique ⟨?_, ?_⟩ ⟨hpk, hpk'⟩
      · rw [Hom.fst_map, hr₁, base_compTo _ _ _ _ _ (hxp k) hRp]
        simp
      · change Hom.map (Functor.Restriction.compTo projection g (f k) hg
          (xr k) (xrij i j) ≫ (xr k).hom) W r = p
        rw [Functor.Restriction.compTo_hom]
        exact hr₂
    have hci := hcomp i _ rfl c he₁ hc pi hpi hpi'
    have hcj := hcomp j _ (hVij i j).w d he₂ hd pj hpj hpj'
    rw [← hci, ← hcj]
    exact congrFun (congrFun (congrArg Hom.map hstar) W) r
  have hwit : ∀ (W : Cᵒᵖ) (p : x.Total W)
      (hp : ((Sieve.ofArrows V f).pullback (eqToHom hxb)).arrows p.1),
      ∃ (i : I) (c : W.unop ⟶ V i) (_ : p.1 = c ≫ f i ≫ eqToHom hxb.symm)
        (p' : (xr i).pt.Total W), p'.1 = c ≫ eqToHom (hxp i).symm ∧
          (xr i).hom.map W p' = p := by
    intro W p hp
    obtain ⟨i, c, hc⟩ := (hSiff p.1).1 hp
    obtain ⟨pi, ⟨hpi1, hpi2⟩, -⟩ := hlift i p c hc
    exact ⟨i, c, hc, pi, hpi1, hpi2⟩
  have hΘex : ∀ (W : Cᵒᵖ) (p : x.Total W),
      ((Sieve.ofArrows V f).pullback (eqToHom hxb)).arrows p.1 → ∃ sec : y.Total W,
        ∀ (i : I) (c : W.unop ⟶ V i), p.1 = c ≫ f i ≫ eqToHom hxb.symm →
          ∀ p' : (xr i).pt.Total W, p'.1 = c ≫ eqToHom (hxp i).symm →
            (xr i).hom.map W p' = p → (φ i ≫ (yr i).hom).map W p' = sec := by
    intro W p hp
    obtain ⟨i, c, hc, pi, hpi1, hpi2⟩ := hwit W p hp
    exact ⟨(φ i ≫ (yr i).hom).map W pi,
      fun j d hd pj hpj1 hpj2 => hagree j i p d c hd hc pj pi hpj1 hpj2 hpi1 hpi2⟩
  choose Θ hΘ using hΘex
  have hT₁ : ∀ (W : Cᵒᵖ) (p : x.Total W)
      (hp : ((Sieve.ofArrows V f).pullback (eqToHom hxb)).arrows p.1),
      (Θ W p hp).1 = p.1 ≫ (eqToHom hxb ≫ eqToHom hyb.symm) := by
    intro W p hp
    obtain ⟨i, c, hc, p', hp'1, hp'2⟩ := hwit W p hp
    rw [← hΘ W p hp i c hc p' hp'1 hp'2, Hom.fst_map, hp'1, hΦ i, hax i, hc]
    simp
  have hT₂ : ∀ (W W' : Cᵒᵖ) (h : W ⟶ W') (p : x.Total W)
      (hp : ((Sieve.ofArrows V f).pullback (eqToHom hxb)).arrows p.1)
      (hp' : ((Sieve.ofArrows V f).pullback (eqToHom hxb)).arrows (x.totalMap h p).1),
      y.totalMap h (Θ W p hp) = Θ W' (x.totalMap h p) hp' := by
    intro W W' h p hp hp'
    obtain ⟨i, c, hc, p', hp'1, hp'2⟩ := hwit W p hp
    have hc2 : (x.totalMap h p).1 = (h.unop ≫ c) ≫ f i ≫ eqToHom hxb.symm := by
      rw [totalMap_fst, hc, Category.assoc]
    have hb1 : ((xr i).pt.totalMap h p').1 = (h.unop ≫ c) ≫ eqToHom (hxp i).symm := by
      rw [totalMap_fst, hp'1, Category.assoc]
    have hb2 : (xr i).hom.map W' ((xr i).pt.totalMap h p') = x.totalMap h p := by
      rw [(xr i).hom.map_naturality h p', hp'2]
    rw [← hΘ W p hp i c hc p' hp'1 hp'2,
      ← hΘ W' (x.totalMap h p) hp' i (h.unop ≫ c) hc2 _ hb1 hb2]
    exact ((φ i ≫ (yr i).hom).map_naturality h p').symm
  have hT₃ : ∀ (W : Cᵒᵖ) (γ : 𝒢.presheaf.obj W) (p : x.Total W)
      (hp : ((Sieve.ofArrows V f).pullback (eqToHom hxb)).arrows p.1)
      (hp' : ((Sieve.ofArrows V f).pullback (eqToHom hxb)).arrows (x.totalSmul γ p).1),
      Θ W (x.totalSmul γ p) hp' = y.totalSmul γ (Θ W p hp) := by
    intro W γ p hp hp'
    obtain ⟨i, c, hc, p', hp'1, hp'2⟩ := hwit W p hp
    have hc2 : (x.totalSmul γ p).1 = c ≫ f i ≫ eqToHom hxb.symm := by
      rw [totalSmul_fst, hc]
    have hb1 : ((xr i).pt.totalSmul γ p').1 = c ≫ eqToHom (hxp i).symm := by
      rw [totalSmul_fst, hp'1]
    have hb2 : (xr i).hom.map W ((xr i).pt.totalSmul γ p') = x.totalSmul γ p := by
      rw [(xr i).hom.map_equivariant W γ p', hp'2]
    rw [← hΘ W p hp i c hc p' hp'1 hp'2,
      ← hΘ W (x.totalSmul γ p) hp' i c hc2 _ hb1 hb2]
    exact (φ i ≫ (yr i).hom).map_equivariant W γ p'
  have hT₄ : ∀ (W : Cᵒᵖ) (p q : x.Total W)
      (hp : ((Sieve.ofArrows V f).pullback (eqToHom hxb)).arrows p.1)
      (hq : ((Sieve.ofArrows V f).pullback (eqToHom hxb)).arrows q.1),
      p.1 = q.1 → Θ W p hp = Θ W q hq → p = q := by
    intro W p q hp hq h1 h2
    obtain ⟨i, c, hc, p', hp'1, hp'2⟩ := hwit W p hp
    obtain ⟨q', ⟨hq'1, hq'2⟩, -⟩ := hlift i q c (h1.symm.trans hc)
    have hkey : (φ i ≫ (yr i).hom).map W p' = (φ i ≫ (yr i).hom).map W q' := by
      rw [hΘ W p hp i c hc p' hp'1 hp'2,
        hΘ W q hq i c (h1.symm.trans hc) q' hq'1 hq'2, h2]
    have hpq : p' = q' :=
      ((φ i ≫ (yr i).hom).bijOn_map W (c ≫ eqToHom (hxp i).symm)).injOn hp'1 hq'1 hkey
    rw [← hp'2, ← hq'2, hpq]
  have hT₅ : ∀ (W : Cᵒᵖ) (a : W.unop ⟶ x.base),
      ((Sieve.ofArrows V f).pullback (eqToHom hxb)).arrows a → ∀ sec : y.Total W,
      sec.1 = a ≫ (eqToHom hxb ≫ eqToHom hyb.symm) →
      ∃ p : x.Total W, ∃ hp : ((Sieve.ofArrows V f).pullback (eqToHom hxb)).arrows p.1,
        p.1 = a ∧ Θ W p hp = sec := by
    intro W a ha sec hs
    obtain ⟨i, c, hca⟩ := (hSiff a).1 ha
    obtain ⟨p', hp'1, hp's⟩ := ((φ i ≫ (yr i).hom).bijOn_map W
        (c ≫ eqToHom (hxp i).symm)).surjOn
      (show sec.1 = (c ≫ eqToHom (hxp i).symm) ≫ Hom.base (φ i ≫ (yr i).hom) by
        rw [hs, hca, hΦ i, hax i]
        simp)
    have hpa : ((xr i).hom.map W p').1 = a := by
      rw [Hom.fst_map, hp'1, hax i, hca]
      simp
    have hpS : ((Sieve.ofArrows V f).pullback (eqToHom hxb)).arrows
        ((xr i).hom.map W p').1 := by
      rw [hpa]
      exact ha
    refine ⟨(xr i).hom.map W p', hpS, hpa, ?_⟩
    rw [← hΘ W ((xr i).hom.map W p') hpS i c (hpa.trans hca) p' hp'1 rfl]
    exact hp's
  obtain ⟨g, hg, hgu⟩ := existsUnique_hom_of_sieve (eqToHom hxb ≫ eqToHom hyb.symm) hS
    (fun p hp => Θ _ p hp) (fun p hp => hT₁ _ p hp) (fun h p hp hp' => hT₂ _ _ h p hp hp')
    (fun γ p hp hp' => hT₃ _ γ p hp hp') (fun p q hp hq => hT₄ _ p q hp hq)
    (fun a ha sec hs => hT₅ _ a ha sec hs)
  refine ⟨g, ⟨isHomLift_of_base g hg.1, isIso_of_base_eq g hg.1, ?_⟩, ?_⟩
  · intro i
    refine Hom.ext ?_ (funext fun W => funext fun p' => ?_)
    · change Hom.base (xr i).hom ≫ Hom.base g = Hom.base (φ i ≫ (yr i).hom)
      rw [hg.1, hΦ i]
    · have hc : ((xr i).hom.map W p').1 =
          (p'.1 ≫ eqToHom (hxp i)) ≫ f i ≫ eqToHom hxb.symm := by
        rw [Hom.fst_map, hax i]
        simp
      have hp1 : p'.1 = (p'.1 ≫ eqToHom (hxp i)) ≫ eqToHom (hxp i).symm := by simp
      have hSp : ((Sieve.ofArrows V f).pullback (eqToHom hxb)).arrows
          ((xr i).hom.map W p').1 := (hSiff _).2 ⟨i, _, hc⟩
      change g.map W ((xr i).hom.map W p') = (φ i ≫ (yr i).hom).map W p'
      rw [hg.2 ((xr i).hom.map W p') hSp]
      exact (hΘ W ((xr i).hom.map W p') hSp i _ hc p' hp1 rfl).symm
  · intro g' hg'
    refine hgu g' ⟨base_eq_of_isHomLift g' hg'.1, fun p hp => ?_⟩
    obtain ⟨i, c, hc, p', hp'1, hp'2⟩ := hwit _ p hp
    exact (congrArg (g'.map _) hp'2.symm).trans
      ((congrFun (congrFun (congrArg Hom.map (hg'.2.2 i)) _) p').trans
        (hΘ _ p hp i c hc p' hp'1 hp'2))

/-- The canonical comparison with a restriction along an identity is the cartesian morphism of the
restriction being compared: the restriction of an object of `𝒢-Torsors` along `𝟙 V` has the
identity as its cartesian morphism, so the defining factorization of the comparison reads as the
comparison itself. -/
theorem compTo_restrictionId {W V : C} (g : W ⟶ V) {T : Torsors.{t} 𝒢}
    {hT : projection.obj T = V} {h : W ⟶ V} (hh : h = g ≫ 𝟙 V)
    (Tr : Functor.Restriction projection h T hT) :
    Functor.Restriction.compTo projection g (𝟙 V) hh
        (Functor.Restriction.id projection T hT) Tr = Tr.hom := by
  refine Eq.trans ?_ (Functor.Restriction.compTo_hom projection g (𝟙 V) hh
    (Functor.Restriction.id projection T hT) Tr)
  exact (Category.comp_id _).symm

/-- **Effectivity of a descent datum for `p : 𝒢-Torsors ⥤ C` out of a glueing of its objects.**
Let `D` be a descent datum for `p` relative to a family `{f i : V i ⟶ U}` with genuine
fibre-product overlaps, let `x` be an object of `𝒢-Torsors` over `U`, and let `χ i : D.x i ⟶ x`
be morphisms of `𝒢-Torsors` lying over the `f i` which are compatible with the glueing
isomorphisms of `D`, in the sense that over each overlap `V i ×_U V j` the square
`D.φ i j ≫ (D.xrji i j).hom ≫ χ j = (D.xrij i j).hom ≫ χ i` commutes. Then `D` is effective.

Everything the effectivity of `D` asks for beyond `x` and the `χ i` is supplied by the universal
property of cartesian morphisms: the restrictions of `x` to the `V i` and to the overlaps exist
because `p` is fibred in groupoids (Stacks 04UK, condition (1)); the fibre morphisms
`x|_{V i} ⟶ D.x i`, and their restrictions `x|_{V i ×_U V j} ⟶ D.x i |_{V i ×_U V j}` to the
overlaps, are the fill-ins of the `χ i` and of `(D.xrij i j).hom`, hence are isomorphisms because
they lie over identities of `C`; and the compatibility `ψir ≫ D.φ i j = ψjr` holds because both
sides become the cartesian morphism of `x|_{V i ×_U V j}` after composition with
`(D.xrji i j).hom ≫ χ j`, which is strongly cartesian and therefore cancels. -/
theorem isEffective_of_glueing {U : C} {I : Type s} (V : I → C) (f : ∀ i, V i ⟶ U)
    (Vij : I → I → C) (pr₁ : ∀ i j, Vij i j ⟶ V i) (pr₂ : ∀ i j, Vij i j ⟶ V j)
    (hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j))
    (Vijk : I → I → I → C)
    (s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j) (s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k)
    (hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k))
    (q₁ : ∀ i j k, Vijk i j k ⟶ V i) (q₂ : ∀ i j k, Vijk i j k ⟶ V j)
    (q₃ : ∀ i j k, Vijk i j k ⟶ V k)
    (hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j)
    (hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j)
    (hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k)
    (D : Functor.DescentDatum (projection : Torsors.{t} 𝒢 ⥤ C) V f Vij pr₁ pr₂ hVij Vijk
      s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃)
    (x : Torsors.{t} 𝒢) (hx : projection.obj x = U) (χ : ∀ i, D.x i ⟶ x)
    (hχ : ∀ i, projection.IsHomLift (eqToHom (D.hx i) ≫ f i ≫ eqToHom hx.symm) (χ i))
    (hglue : ∀ i j, D.φ i j ≫ (D.xrji i j).hom ≫ χ j = (D.xrij i j).hom ≫ χ i) :
    D.IsEffective := by
  have hgpd : (projection : Torsors.{t} 𝒢 ⥤ C).IsFiberedInGroupoids :=
    projection_isFiberedInGroupoids
  have hxb : x.base = U := hx
  have hDb : ∀ i, (D.x i).base = V i := fun i => D.hx i
  have hχb : ∀ i, Hom.base (χ i) = eqToHom (hDb i) ≫ f i ≫ eqToHom hxb.symm :=
    fun i => base_eq_of_isHomLift _ (hχ i)
  have xr : ∀ i, Functor.Restriction projection (f i) x hx := fun i =>
    Functor.Restriction.ofIsFiberedInGroupoids projection hgpd (f i) x hx
  have hxrp : ∀ i, (xr i).pt.base = V i := fun i => (xr i).hpt
  have hxrb : ∀ i, Hom.base (xr i).hom = eqToHom (hxrp i) ≫ f i ≫ eqToHom hxb.symm :=
    fun i => base_eq_of_isHomLift _ (xr i).isHomLift
  have hex : ∀ {A B R : Torsors.{t} 𝒢} (a : A ⟶ B) (b : R ⟶ B) (e : R.base ⟶ A.base),
      e ≫ Hom.base a = Hom.base b → ∃ ψ : R ⟶ A, Hom.base ψ = e ∧ ψ ≫ a = b := by
    intro A B R a b e h
    obtain ⟨ψ, ⟨h₁, h₂⟩, -⟩ := hgpd.unique_lift a b e h
    exact ⟨ψ, h₁, h₂⟩
  have hψex : ∀ i, ∃ ψ : (xr i).pt ⟶ D.x i,
      Hom.base ψ = eqToHom (hxrp i) ≫ eqToHom (hDb i).symm ∧ ψ ≫ χ i = (xr i).hom := by
    intro i
    have hcomm : (eqToHom (hxrp i) ≫ eqToHom (hDb i).symm) ≫ Hom.base (χ i) =
        Hom.base (xr i).hom := by
      rw [hχb i, hxrb i]
      simp
    exact hex (χ i) (xr i).hom _ hcomm
  choose ψ hψb hψχ using hψex
  refine ⟨x, hx, xr, ψ, fun i => isHomLift_of_base (ψ i) (hψb i),
    fun i => isIso_of_base_eq (ψ i) (hψb i), fun i j => ?_⟩
  have R : Functor.Restriction projection (pr₁ i j ≫ f i) x hx :=
    Functor.Restriction.ofIsFiberedInGroupoids projection hgpd (pr₁ i j ≫ f i) x hx
  have hRp : R.pt.base = Vij i j := R.hpt
  have hRijp : (D.xrij i j).pt.base = Vij i j := (D.xrij i j).hpt
  have hRjip : (D.xrji i j).pt.base = Vij i j := (D.xrji i j).hpt
  have hci : Hom.base (Functor.Restriction.compTo projection (pr₁ i j) (f i) rfl (xr i) R) =
      eqToHom hRp ≫ pr₁ i j ≫ eqToHom (hxrp i).symm :=
    base_compTo (pr₁ i j) (f i) rfl (xr i) R (hxrp i) hRp
  have hcj : Hom.base (Functor.Restriction.compTo projection (pr₂ i j) (f j) (hVij i j).w
        (xr j) R) = eqToHom hRp ≫ pr₂ i j ≫ eqToHom (hxrp j).symm :=
    base_compTo (pr₂ i j) (f j) (hVij i j).w (xr j) R (hxrp j) hRp
  have hbij : Hom.base (D.xrij i j).hom =
      eqToHom hRijp ≫ pr₁ i j ≫ eqToHom (hDb i).symm :=
    base_eq_of_isHomLift _ (D.xrij i j).isHomLift
  have hbji : Hom.base (D.xrji i j).hom =
      eqToHom hRjip ≫ pr₂ i j ≫ eqToHom (hDb j).symm :=
    base_eq_of_isHomLift _ (D.xrji i j).isHomLift
  have hbφ : Hom.base (D.φ i j) = eqToHom hRijp ≫ eqToHom hRjip.symm :=
    base_eq_of_isHomLift _ (D.φ_fibreHom i j)
  have hirex : ∃ ψir : R.pt ⟶ (D.xrij i j).pt,
      Hom.base ψir = eqToHom hRp ≫ eqToHom hRijp.symm ∧
        ψir ≫ (D.xrij i j).hom =
          Functor.Restriction.compTo projection (pr₁ i j) (f i) rfl (xr i) R ≫ ψ i := by
    have hcomm : (eqToHom hRp ≫ eqToHom hRijp.symm) ≫ Hom.base (D.xrij i j).hom =
        Hom.base (Functor.Restriction.compTo projection (pr₁ i j) (f i) rfl (xr i) R) ≫
          Hom.base (ψ i) := by
      rw [hbij, hci, hψb i]
      simp
    exact hex (D.xrij i j).hom _ _ hcomm
  obtain ⟨ψir, hirb, hirfac⟩ := hirex
  have hjrex : ∃ ψjr : R.pt ⟶ (D.xrji i j).pt,
      Hom.base ψjr = eqToHom hRp ≫ eqToHom hRjip.symm ∧
        ψjr ≫ (D.xrji i j).hom = Functor.Restriction.compTo projection (pr₂ i j) (f j)
          (hVij i j).w (xr j) R ≫ ψ j := by
    have hcomm : (eqToHom hRp ≫ eqToHom hRjip.symm) ≫ Hom.base (D.xrji i j).hom =
        Hom.base (Functor.Restriction.compTo projection (pr₂ i j) (f j) (hVij i j).w
          (xr j) R) ≫ Hom.base (ψ j) := by
      rw [hbji, hcj, hψb j]
      simp
    exact hex (D.xrji i j).hom _ _ hcomm
  obtain ⟨ψjr, hjrb, hjrfac⟩ := hjrex
  refine ⟨R, ψir, ψjr, isHomLift_of_base ψir hirb, isHomLift_of_base ψjr hjrb,
    isIso_of_base_eq ψir hirb, isIso_of_base_eq ψjr hjrb, ?_, ?_, ?_⟩
  · change ψir ≫ Functor.Restriction.compTo projection (pr₁ i j) (𝟙 (V i)) (by simp)
        (Functor.Restriction.id projection (D.x i) (D.hx i)) (D.xrij i j) =
      Functor.Restriction.compTo projection (pr₁ i j) (f i) rfl (xr i) R ≫ ψ i
    rw [compTo_restrictionId]
    exact hirfac
  · change ψjr ≫ Functor.Restriction.compTo projection (pr₂ i j) (𝟙 (V j)) (by simp)
        (Functor.Restriction.id projection (D.x j) (D.hx j)) (D.xrji i j) =
      Functor.Restriction.compTo projection (pr₂ i j) (f j) (hVij i j).w (xr j) R ≫ ψ j
    rw [compTo_restrictionId]
    exact hjrfac
  · have hl₁ : projection.IsHomLift (eqToHom hRp ≫ eqToHom hRjip.symm) (ψir ≫ D.φ i j) := by
      refine isHomLift_of_base _ ?_
      rw [show Hom.base (ψir ≫ D.φ i j) = Hom.base ψir ≫ Hom.base (D.φ i j) from rfl,
        hirb, hbφ]
      simp
    have hl₂ : projection.IsHomLift (eqToHom hRp ≫ eqToHom hRjip.symm) ψjr :=
      isHomLift_of_base ψjr hjrb
    have hl₃ : projection.IsHomLift (eqToHom hRp ≫ pr₂ i j ≫ eqToHom (hDb j).symm)
        ((ψir ≫ D.φ i j) ≫ (D.xrji i j).hom) := by
      refine isHomLift_of_base _ ?_
      rw [show Hom.base ((ψir ≫ D.φ i j) ≫ (D.xrji i j).hom) =
          (Hom.base ψir ≫ Hom.base (D.φ i j)) ≫ Hom.base (D.xrji i j).hom from rfl,
        hirb, hbφ, hbji]
      simp
    have hl₄ : projection.IsHomLift (eqToHom hRp ≫ pr₂ i j ≫ eqToHom (hDb j).symm)
        (ψjr ≫ (D.xrji i j).hom) := by
      refine isHomLift_of_base _ ?_
      rw [show Hom.base (ψjr ≫ (D.xrji i j).hom) =
          Hom.base ψjr ≫ Hom.base (D.xrji i j).hom from rfl, hjrb, hbji]
      simp
    have hcartji : projection.IsStronglyCartesian
        (eqToHom hRjip ≫ pr₂ i j ≫ eqToHom (hDb j).symm) (D.xrji i j).hom := (D.xrji i j).isCart
    have hlχ : projection.IsHomLift (eqToHom (hDb j) ≫ f j ≫ eqToHom hxb.symm) (χ j) :=
      isHomLift_of_base (χ j) (hχb j)
    have hcartχ : projection.IsStronglyCartesian
        (eqToHom (hDb j) ≫ f j ≫ eqToHom hxb.symm) (χ j) :=
      hgpd.isStronglyCartesian_homLift _ (χ j)
    have h₁ : ((ψir ≫ D.φ i j) ≫ (D.xrji i j).hom) ≫ χ j = R.hom := by
      simp only [Category.assoc]
      rw [hglue i j, ← Category.assoc, hirfac, Category.assoc, hψχ i]
      exact Functor.Restriction.compTo_hom projection (pr₁ i j) (f i) rfl (xr i) R
    have h₂ : (ψjr ≫ (D.xrji i j).hom) ≫ χ j = R.hom := by
      rw [hjrfac, Category.assoc, hψχ j]
      exact Functor.Restriction.compTo_hom projection (pr₂ i j) (f j) (hVij i j).w (xr j) R
    have hstep : (ψir ≫ D.φ i j) ≫ (D.xrji i j).hom = ψjr ≫ (D.xrji i j).hom :=
      Functor.IsStronglyCartesian.ext projection
        (eqToHom (hDb j) ≫ f j ≫ eqToHom hxb.symm) (χ j)
        (eqToHom hRp ≫ pr₂ i j ≫ eqToHom (hDb j).symm) (h₁.trans h₂.symm)
    exact Functor.IsStronglyCartesian.ext projection
      (eqToHom hRjip ≫ pr₂ i j ≫ eqToHom (hDb j).symm) (D.xrji i j).hom
      (eqToHom hRp ≫ eqToHom hRjip.symm) hstep

end SheafOfGroups.Torsors

end
