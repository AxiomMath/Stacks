module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.StackOfTorsors.GluedPresheaf
import StacksCore.Tactic.StacksAttribute

/-!
# Effective descent for torsors, and the stack of torsors

The presheaf glued from a descent datum for `p : 𝒢-Torsors ⥤ C` is a sheaf
(`SheafOfGroups.Torsors.Descent.gluedPresheaf_isSheaf`) carrying a torsor structure
(`SheafOfGroups.Torsors.Descent.gluedTorsorObj`); this gives condition (3) of Stacks 02ZI
(`SheafOfGroups.Torsors.projection_effectiveDescent`), and
`SheafOfGroups.Torsors.projection_isStackInGroupoids` assembles the three conditions
(Stacks 04UK).
-/

@[expose] public section

open CategoryTheory Opposite

universe t w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace SheafOfGroups.Torsors

variable {𝒢 : SheafOfGroups.{w} (C := C) J}

universe s

/-- The identity section of `𝒢` acts trivially on the total space of a torsor. -/
theorem totalSmul_one (T : Torsors.{t} 𝒢) {W : Cᵒᵖ} (p : T.Total W) : T.totalSmul 1 p = p :=
  congrArg (Sigma.mk p.1) (T.torsor.one_act (op (Over.mk p.1)) p.2)

/-- The action of `𝒢` on the total space of a torsor is compatible with multiplication. -/
theorem totalSmul_mul (T : Torsors.{t} 𝒢) {W : Cᵒᵖ} (γ δ : 𝒢.presheaf.obj W) (p : T.Total W) :
    T.totalSmul (γ * δ) p = T.totalSmul γ (T.totalSmul δ p) :=
  congrArg (Sigma.mk p.1) (T.torsor.mul_act (op (Over.mk p.1)) γ δ p.2)

/-- **The action of `𝒢` on each fibre of the total space of a torsor is simply transitive.**
Two elements of the total space of a torsor lying over the same morphism of the base differ by
a unique section of `𝒢`. -/
theorem totalSmul_existsUnique (T : Torsors.{t} 𝒢) {W : Cᵒᵖ} (p q : T.Total W)
    (h : p.1 = q.1) : ∃! γ : 𝒢.presheaf.obj W, T.totalSmul γ p = q := by
  obtain ⟨γ, hγ, hγu⟩ := T.torsor.simplyTransitive (op (Over.mk p.1)) ⟨p.2⟩ p.2
    (T.secOver q h.symm)
  have hiff : ∀ δ : 𝒢.presheaf.obj W, T.totalSmul δ p = q ↔
      T.torsor.act (op (Over.mk p.1)) δ p.2 = T.secOver q h.symm := by
    refine fun δ => ⟨fun hd => ?_, fun hd => ?_⟩
    · exact (T.secOver_mk p.1 (T.torsor.act (op (Over.mk p.1)) δ p.2)).symm.trans
        (T.secOver_congr (γ := p.1) (r := T.totalSmul δ p) rfl h.symm hd)
    · exact T.secOver_injective (γ := p.1) rfl h.symm
        ((T.secOver_mk p.1 (T.torsor.act (op (Over.mk p.1)) δ p.2)).trans hd)
  exact ⟨γ, (hiff γ).2 hγ, fun δ hδ => hγu δ ((hiff δ).1 hδ)⟩

namespace Descent

variable {U : C} {I : Type s} {V : I → C} {f : ∀ i, V i ⟶ U}
  {Vij : I → I → C} {pr₁ : ∀ i j, Vij i j ⟶ V i} {pr₂ : ∀ i j, Vij i j ⟶ V j}
  {hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j)}
  {Vijk : I → I → I → C}
  {s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j} {s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k}
  {hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k)}
  {q₁ : ∀ i j k, Vijk i j k ⟶ V i} {q₂ : ∀ i j k, Vijk i j k ⟶ V j}
  {q₃ : ∀ i j k, Vijk i j k ⟶ V k}
  {hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j}
  {hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j}
  {hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k}
  (D : Functor.DescentDatum (projection : Torsors.{t} 𝒢 ⥤ C) V f Vij pr₁ pr₂ hVij
    Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃)

/-- **Glueing sections of the presheaf glued from a descent datum.** A family of sections
indexed by a covering sieve of `W`, compatible with the restriction maps, has a unique
amalgamation. The amalgamation is built one attached element at a time by the sheaf condition
for the corresponding `D.x i`, and the witnesses of the transitions over the overlaps are glued
in the same way. -/
theorem exists_glued_amalgamation (W : C) (β : W ⟶ U) (T : Sieve W) (hT : T ∈ J W)
    (FF : ∀ {Z : C} (k : Z ⟶ W), T k → Glued D (k ≫ β))
    (hFF : ∀ {Z Z' : C} (k : Z ⟶ W) (hk : T k) (k' : Z' ⟶ W) (hk' : T k') (n : Z' ⟶ Z)
      (_ : n ≫ k = k') (i : I) (Z'' : C) (m : Z'' ⟶ Z') (m' : Z'' ⟶ Z) (_ : m ≫ n = m')
      (d : Z'' ⟶ V i) (ha : m ≫ (k' ≫ β) = d ≫ f i) (hb : m' ≫ (k ≫ β) = d ≫ f i),
      (FF k' hk').sec i Z'' m d ha = (FF k hk).sec i Z'' m' d hb) :
    ∃! G : Glued D β, ∀ (i : I) (Z Z' : C) (k : Z ⟶ W) (hk : T k) (m : Z' ⟶ Z)
      (m' : Z' ⟶ W) (_ : m ≫ k = m') (d : Z' ⟶ V i)
      (ha : m ≫ (k ≫ β) = d ≫ f i) (hb : m' ≫ β = d ≫ f i),
      (FF k hk).sec i Z' m d ha = G.sec i Z' m' d hb := by
  have hloc : ∀ (i : I) (Z : C) (g : Z ⟶ W) (c : Z ⟶ V i) (h : g ≫ β = c ≫ f i),
      ∃ r : (D.x i).Total (op Z), r.1 = c ≫ eqToHom (base_x D i).symm ∧
        ∀ (Z' : C) (l : Z' ⟶ Z) (k' : Z' ⟶ W) (hk : l ≫ g = k') (hl : T k')
          (d : Z' ⟶ V i) (hd : l ≫ c = d),
          (D.x i).totalMap l.op r = (FF k' hl).sec i Z' (𝟙 Z') d (by simp [← hk, ← hd, h]) := by
    intro i Z g c h
    obtain ⟨r, ⟨hr₁, hr₂⟩, -⟩ := (D.x i).existsUnique_total (W := op Z)
      (c ≫ eqToHom (base_x D i).symm) (S := T.pullback g) (J.pullback_stable g hT)
      (fun {Z'} l hl => (FF (l.unop ≫ g) hl).sec i Z'.unop (𝟙 Z'.unop) (l.unop ≫ c)
        (by simp [h]))
      (fun {Z'} l hl => by rw [(FF (l.unop ≫ g) hl).base_sec, Category.assoc])
      (fun {Z'} {Z''} l hl n hn => by
        refine ((FF (l.unop ≫ g) hl).sec_restrict i Z'.unop Z''.unop n.unop (𝟙 Z'.unop)
          (l.unop ≫ c) _ (by simp [h])).trans ?_
        have hy : n.unop ≫ ((l.unop ≫ g) ≫ β) = ((n.unop ≫ l.unop) ≫ c) ≫ f i := by
          simp [h]
        refine (Glued.sec_congr D (FF (l.unop ≫ g) hl) i Z''.unop (Category.comp_id n.unop)
          (Category.assoc n.unop l.unop c).symm _ hy).trans ?_
        exact (hFF (l.unop ≫ g) hl ((n.unop ≫ l.unop) ≫ g) hn n.unop
          (Category.assoc n.unop l.unop g).symm i Z''.unop (𝟙 Z''.unop) n.unop
          (Category.id_comp n.unop) ((n.unop ≫ l.unop) ≫ c) (by simp [h]) hy).symm)
    refine ⟨r, hr₁, fun Z' l k' hk' hl d hd => ?_⟩
    subst hk'
    subst hd
    exact hr₂ l.op hl
  choose Sec hSec₁ hSec₂ using hloc
  have hext : ∀ (i : I) (Z : C) (g : Z ⟶ W) {r r' : (D.x i).Total (op Z)}, r.1 = r'.1 →
      (∀ {Z' : C} (l : Z' ⟶ Z), T (l ≫ g) → (D.x i).totalMap l.op r = (D.x i).totalMap l.op r') →
      r = r' :=
    fun i Z g _ _ h₁ h₂ => (D.x i).total_ext (S := T.pullback g) (J.pullback_stable g hT) h₁
      fun h hh => h₂ h.unop hh
  have hrestrict : ∀ (i : I) (Z Z' : C) (k : Z' ⟶ Z) (g : Z ⟶ W) (c : Z ⟶ V i)
      (h : g ≫ β = c ≫ f i) (h' : (k ≫ g) ≫ β = (k ≫ c) ≫ f i),
      (D.x i).totalMap k.op (Sec i Z g c h) = Sec i Z' (k ≫ g) (k ≫ c) h' := by
    intro i Z Z' k g c h h'
    refine hext i Z' (k ≫ g) ?_ fun {Z''} l hl => ?_
    · rw [totalMap_fst, hSec₁, hSec₁]
      exact (Category.assoc k c (eqToHom (base_x D i).symm)).symm
    · refine Eq.trans ?_ (hSec₂ i Z' (k ≫ g) (k ≫ c) h' Z'' l _ rfl hl _ rfl).symm
      refine Eq.trans ?_ (hSec₂ i Z g c h Z'' (l ≫ k) _ (Category.assoc l k g) hl _
        (Category.assoc l k c))
      exact (D.x i).totalMap_comp k.op l.op (Sec i Z g c h)
  have htrans : ∀ (i j : I) (Z : C) (g : Z ⟶ W) (e : Z ⟶ Vij i j)
      (h : g ≫ β = (e ≫ pr₁ i j) ≫ f i) (h' : g ≫ β = (e ≫ pr₂ i j) ≫ f j),
      IsTransition D i j Z e (Sec i Z g (e ≫ pr₁ i j) h) (Sec j Z g (e ≫ pr₂ i j) h') := by
    intro i j Z g e h h'
    obtain ⟨qq, hqq⟩ := exists_isTransition D i j Z e (Sec i Z g (e ≫ pr₁ i j) h)
      (hSec₁ i Z g (e ≫ pr₁ i j) h)
    have hfin : qq = Sec j Z g (e ≫ pr₂ i j) h' := by
      refine hext j Z g ?_ fun {Z'} l hl => ?_
      · rw [IsTransition.base_tgt D hqq, hSec₁]
      · have hB := Glued.transition D (FF (l ≫ g) hl) i j Z' (𝟙 Z') (l ≫ e)
          (Category.assoc l e (pr₁ i j)) (Category.assoc l e (pr₂ i j)) (by simp [h])
          (by simp [h'])
        rw [← hSec₂ i Z g (e ≫ pr₁ i j) h Z' l _ rfl hl _ rfl,
          ← hSec₂ j Z g (e ≫ pr₂ i j) h' Z' l _ rfl hl _ rfl] at hB
        exact IsTransition.unique D (IsTransition.restrict D hqq l) hB
    rw [← hfin]
    exact hqq
  refine ⟨⟨Sec, hSec₁, hrestrict, htrans⟩, ?_, ?_⟩
  · intro i Z Z' k hk m m' hm d ha hb
    subst hm
    have hb' : m ≫ (k ≫ β) = d ≫ f i := (Category.assoc m k β).symm.trans hb
    refine (hext i Z' (m ≫ k) ?_ fun {Z''} l hl => ?_).symm
    · rw [hSec₁, (FF k hk).base_sec]
    · have hB : (l ≫ m) ≫ (k ≫ β) = (l ≫ d) ≫ f i := by simp [hb']
      refine Eq.trans (hSec₂ i Z' (m ≫ k) d hb Z'' l _ rfl hl _ rfl) ?_
      refine Eq.trans (hFF k hk (l ≫ (m ≫ k)) hl (l ≫ m)
        (Category.assoc l m k) i Z'' (𝟙 Z'') (l ≫ m)
        (Category.id_comp (l ≫ m)) (l ≫ d) (by simp [hb']) hB) ?_
      exact ((FF k hk).sec_restrict i Z' Z'' l m d ha hB).symm
  · intro G' hG'
    refine Glued.ext' D fun i Z g c hc => ?_
    refine hext i Z g ?_ fun {Z'} l hl => ?_
    · rw [G'.base_sec, hSec₁]
    · have hB : (l ≫ g) ≫ β = (l ≫ c) ≫ f i := by simp [hc]
      refine Eq.trans (G'.sec_restrict i Z Z' l g c hc hB) ?_
      refine Eq.trans (hG' i Z' Z' (l ≫ g) hl (𝟙 Z') (l ≫ g)
        (Category.id_comp (l ≫ g)) (l ≫ c) (by simp [hc]) hB).symm ?_
      exact (hSec₂ i Z g c hc Z' l _ rfl hl _ rfl).symm

end Descent

namespace Descent

variable {U : C} {I : Type s} {V : I → C} {f : ∀ i, V i ⟶ U}
  {Vij : I → I → C} {pr₁ : ∀ i j, Vij i j ⟶ V i} {pr₂ : ∀ i j, Vij i j ⟶ V j}
  {hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j)}
  {Vijk : I → I → I → C}
  {s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j} {s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k}
  {hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k)}
  {q₁ : ∀ i j k, Vijk i j k ⟶ V i} {q₂ : ∀ i j k, Vijk i j k ⟶ V j}
  {q₃ : ∀ i j k, Vijk i j k ⟶ V k}
  {hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j}
  {hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j}
  {hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k}
  (D : Functor.DescentDatum (projection : Torsors.{t} 𝒢 ⥤ C) V f Vij pr₁ pr₂ hVij
    Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃)

/-- **The presheaf glued from a descent datum is a sheaf on the localized site `C/U`.** A
compatible family of its sections over a covering sieve is, through the equivalence between
sieves of `(W, β)` and sieves of `W`, a compatible family of matching families, and such a
family has a unique amalgamation. -/
theorem gluedPresheaf_isSheaf : Presheaf.IsSheaf (J.over U) (gluedPresheaf D) := by
  rw [CategoryTheory.isSheaf_iff_isSheaf_of_type]
  intro Y S hS fam hfam
  have hT : Sieve.overEquiv Y S ∈ J Y.left := (J.mem_over_iff S).1 hS
  have hFF : ∀ {Z Z' : C} (k : Z ⟶ Y.left) (hk : (Sieve.overEquiv Y S) k)
      (k' : Z' ⟶ Y.left) (hk' : (Sieve.overEquiv Y S) k') (n : Z' ⟶ Z) (_ : n ≫ k = k')
      (i : I) (Z'' : C) (m : Z'' ⟶ Z') (m' : Z'' ⟶ Z) (_ : m ≫ n = m') (d : Z'' ⟶ V i)
      (ha : m ≫ (k' ≫ Y.hom) = d ≫ f i) (hb : m' ≫ (k ≫ Y.hom) = d ≫ f i),
      (fam (Over.homMk k' : Over.mk (k' ≫ Y.hom) ⟶ Y)
          ((Sieve.overEquiv_iff S k').1 hk')).sec i Z'' m d ha =
        (fam (Over.homMk k : Over.mk (k ≫ Y.hom) ⟶ Y)
          ((Sieve.overEquiv_iff S k).1 hk)).sec i Z'' m' d hb := by
    intro Z Z' k hk k' hk' n hn i Z'' m m' hm d ha hb
    subst hn
    subst hm
    have hw : n ≫ (Over.mk (k ≫ Y.hom)).hom = (Over.mk ((n ≫ k) ≫ Y.hom)).hom :=
      (Category.assoc n k Y.hom).symm
    have hb2 : (m ≫ 𝟙 Z') ≫ ((n ≫ k) ≫ Y.hom) = d ≫ f i := by simpa using ha
    have e := hfam (𝟙 (Over.mk ((n ≫ k) ≫ Y.hom)))
      (Over.homMk n hw : Over.mk ((n ≫ k) ≫ Y.hom) ⟶ Over.mk (k ≫ Y.hom))
      ((Sieve.overEquiv_iff S (n ≫ k)).1 hk') ((Sieve.overEquiv_iff S k).1 hk)
      (Over.OverMorphism.ext (by simp))
    have e' := congrArg (fun A : Glued D ((n ≫ k) ≫ Y.hom) => A.sec i Z'' m d ha) e
    refine Eq.trans ?_ (e'.trans (gluedPresheaf_map_sec D
      (Over.homMk n hw : Over.mk ((n ≫ k) ≫ Y.hom) ⟶ Over.mk (k ≫ Y.hom)).op
      (fam (Over.homMk k : Over.mk (k ≫ Y.hom) ⟶ Y) ((Sieve.overEquiv_iff S k).1 hk))
      i Z'' m d ha hb))
    refine Eq.trans ?_ (gluedPresheaf_map_sec D (𝟙 (Over.mk ((n ≫ k) ≫ Y.hom))).op
      (fam (Over.homMk (n ≫ k) : Over.mk ((n ≫ k) ≫ Y.hom) ⟶ Y)
        ((Sieve.overEquiv_iff S (n ≫ k)).1 hk')) i Z'' m d ha hb2).symm
    exact Glued.sec_congr D _ i Z'' (Category.comp_id m).symm rfl ha hb2
  obtain ⟨G, hG, hGu⟩ := exists_glued_amalgamation D Y.left Y.hom (Sieve.overEquiv Y S) hT
    (fun {Z} k hk => fam (Over.homMk k : Over.mk (k ≫ Y.hom) ⟶ Y)
      ((Sieve.overEquiv_iff S k).1 hk)) hFF
  refine ⟨G, ?_, ?_⟩
  · intro Y' u hu
    have hww : 𝟙 Y'.left ≫ Y'.hom = (Over.mk (u.left ≫ Y.hom)).hom :=
      (Category.id_comp Y'.hom).trans (Over.w u).symm
    have hcomp : (Over.homMk (𝟙 Y'.left) hww : Over.mk (u.left ≫ Y.hom) ⟶ Y') ≫ u =
        (Over.homMk u.left : Over.mk (u.left ≫ Y.hom) ⟶ Y) :=
      Over.OverMorphism.ext (by simp)
    have hk' : (Sieve.overEquiv Y S) u.left := by
      refine (Sieve.overEquiv_iff S u.left).2 ?_
      rw [← hcomp]
      exact S.downward_closed hu _
    refine Glued.ext' D fun i Z g c hc => ?_
    have ha : g ≫ (u.left ≫ Y.hom) = c ≫ f i := by rw [Over.w u]; exact hc
    have hb : (g ≫ u.left) ≫ Y.hom = c ≫ f i := by rw [Category.assoc]; exact ha
    have hd1 : (g ≫ 𝟙 Y'.left) ≫ (u.left ≫ Y.hom) = c ≫ f i := by simpa using ha
    have hd2 : (g ≫ 𝟙 Y'.left) ≫ Y'.hom = c ≫ f i := by simpa using hc
    refine Eq.trans (gluedPresheaf_map_sec D u.op G i Z g c hc hb) ?_
    refine Eq.trans (hG i Y'.left Z u.left hk' g (g ≫ u.left) rfl c ha hb).symm ?_
    have e := hfam (𝟙 (Over.mk (u.left ≫ Y.hom)))
      (Over.homMk (𝟙 Y'.left) hww : Over.mk (u.left ≫ Y.hom) ⟶ Y')
      ((Sieve.overEquiv_iff S u.left).1 hk') hu (Over.OverMorphism.ext (by simp [hcomp]))
    have e' := congrArg (fun A : Glued D (u.left ≫ Y.hom) => A.sec i Z g c ha) e
    refine Eq.trans ?_ (e'.trans ?_)
    · refine Eq.trans ?_ (gluedPresheaf_map_sec D (𝟙 (Over.mk (u.left ≫ Y.hom))).op
        (fam (Over.homMk u.left : Over.mk (u.left ≫ Y.hom) ⟶ Y)
          ((Sieve.overEquiv_iff S u.left).1 hk')) i Z g c ha hd1).symm
      exact Glued.sec_congr D _ i Z (Category.comp_id g).symm rfl ha hd1
    · refine Eq.trans (gluedPresheaf_map_sec D
        (Over.homMk (𝟙 Y'.left) hww : Over.mk (u.left ≫ Y.hom) ⟶ Y').op
        (fam u hu) i Z g c ha hd2) ?_
      exact Glued.sec_congr D (fam u hu) i Z (Category.comp_id g) rfl hd2 hc
  · intro G' hG'
    refine hGu G' fun i Z Z' k hk m m' hm d ha hb => ?_
    subst hm
    refine Eq.trans ?_ (gluedPresheaf_map_sec D
      (Over.homMk k : Over.mk (k ≫ Y.hom) ⟶ Y).op G' i Z' m d ha hb)
    exact congrArg (fun A : Glued D (k ≫ Y.hom) => A.sec i Z' m d ha)
      (hG' (Over.homMk k : Over.mk (k ≫ Y.hom) ⟶ Y)
        ((Sieve.overEquiv_iff S k).1 hk)).symm

end Descent

namespace Descent

variable {U : C} {I : Type s} {V : I → C} {f : ∀ i, V i ⟶ U}
  {Vij : I → I → C} {pr₁ : ∀ i j, Vij i j ⟶ V i} {pr₂ : ∀ i j, Vij i j ⟶ V j}
  {hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j)}
  {Vijk : I → I → I → C}
  {s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j} {s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k}
  {hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k)}
  {q₁ : ∀ i j k, Vijk i j k ⟶ V i} {q₂ : ∀ i j k, Vijk i j k ⟶ V j}
  {q₃ : ∀ i j k, Vijk i j k ⟶ V k}
  {hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j}
  {hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j}
  {hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k}
  (D : Functor.DescentDatum (projection : Torsors.{t} 𝒢 ⥤ C) V f Vij pr₁ pr₂ hVij
    Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃)

/-- The action of `𝒢` on the sections of the presheaf glued from a descent datum: a section of
`𝒢` over `W` acts on a matching family over `(W, β)` by acting, through its restriction, on each
attached element. -/
def gluedAct (Y : (Over U)ᵒᵖ) (γ : (𝒢.over U).presheaf.obj Y) (G : Glued D Y.unop.hom) :
    Glued D Y.unop.hom where
  sec i Z g c h := (D.x i).totalSmul (𝒢.presheaf.map g.op γ) (G.sec i Z g c h)
  base_sec i Z g c h := by rw [totalSmul_fst, G.base_sec]
  sec_restrict i Z Z' k g c h h' := by
    rw [(D.x i).totalMap_totalSmul k.op _ (G.sec i Z g c h), G.sec_restrict i Z Z' k g c h h',
      show 𝒢.presheaf.map k.op (𝒢.presheaf.map g.op γ) = 𝒢.presheaf.map (k ≫ g).op γ from
        (𝒢.presheaf.map_comp_apply g.op k.op γ).symm]
  sec_transition i j Z g e h h' :=
    IsTransition.smul D (G.sec_transition i j Z g e h h') (𝒢.presheaf.map g.op γ)

/-- Two sections of the glued presheaf over the same object which differ by a section of `𝒢` at
one factorization differ by it at every factorization: the transitions of a descent datum are
equivariant. -/
theorem glued_smul_of_smul (Y : (Over U)ᵒᵖ) (G H : Glued D Y.unop.hom) (Z : C)
    (g : Z ⟶ Y.unop.left) (γ : 𝒢.presheaf.obj (op Z)) (i₀ : I) (c₀ : Z ⟶ V i₀)
    (hc₀ : g ≫ Y.unop.hom = c₀ ≫ f i₀)
    (hγ : (D.x i₀).totalSmul γ (G.sec i₀ Z g c₀ hc₀) = H.sec i₀ Z g c₀ hc₀) :
    ∀ (i : I) (c : Z ⟶ V i) (h : g ≫ Y.unop.hom = c ≫ f i),
      (D.x i).totalSmul γ (G.sec i Z g c h) = H.sec i Z g c h := by
  intro i c h
  obtain ⟨e, he₁, he₂⟩ := exists_overlapLift (hVij i₀ i) c₀ c (hc₀.symm.trans h)
  have hs := IsTransition.smul D (Glued.transition D G i₀ i Z g e he₁ he₂ hc₀ h) γ
  rw [hγ] at hs
  exact IsTransition.unique D hs (Glued.transition D H i₀ i Z g e he₁ he₂ hc₀ h)

/-- **The action of `𝒢` on the glued presheaf is simply transitive.** Two matching families over
the same object of `C/U` differ by a unique section of `𝒢`: they differ by a unique section over
each member of the covering family, those sections agree on the overlaps because the transitions
of a descent datum are equivariant, and they glue because `𝒢` is a sheaf. -/
theorem glued_simplyTransitive (hf : Sieve.ofArrows V f ∈ J U) (Y : (Over U)ᵒᵖ)
    (G H : Glued D Y.unop.hom) :
    ∃! γ : (𝒢.over U).presheaf.obj Y, gluedAct D Y γ G = H := by
  have hR : (Sieve.ofArrows V f).pullback Y.unop.hom ∈ J Y.unop.left :=
    J.pullback_stable _ hf
  have hγloc : ∀ (Z : C) (g : Z ⟶ Y.unop.left),
      ((Sieve.ofArrows V f).pullback Y.unop.hom) g →
      ∃! γ : 𝒢.presheaf.obj (op Z), ∀ (i : I) (c : Z ⟶ V i)
        (h : g ≫ Y.unop.hom = c ≫ f i),
        (D.x i).totalSmul γ (G.sec i Z g c h) = H.sec i Z g c h := by
    intro Z g hg
    obtain ⟨i₀, c₀, hc₀⟩ := (Sieve.mem_ofArrows_iff V f (g ≫ Y.unop.hom)).1 hg
    obtain ⟨γ, hγ, hγu⟩ := (D.x i₀).totalSmul_existsUnique (G.sec i₀ Z g c₀ hc₀)
      (H.sec i₀ Z g c₀ hc₀) (by rw [G.base_sec, H.base_sec])
    exact ⟨γ, glued_smul_of_smul D Y G H Z g γ i₀ c₀ hc₀ hγ,
      fun δ hδ => hγu δ (hδ i₀ c₀ hc₀)⟩
  choose γloc hγloc₁ hγloc₂ using hγloc
  have hsf : Presieve.IsSheafFor 𝒢.presheaf
      (((Sieve.ofArrows V f).pullback Y.unop.hom) : Presieve Y.unop.left) :=
    (CategoryTheory.isSheaf_iff_isSheaf_of_type _ _).1 𝒢.isSheaf _ hR
  have hex := hsf (fun _ g hg => γloc _ g hg) (by
    refine (Presieve.compatible_iff_sieveCompatible _).2 ?_
    intro Z Z' g k hg
    refine (hγloc₂ Z' (k ≫ g) (((Sieve.ofArrows V f).pullback Y.unop.hom).downward_closed hg k)
      (𝒢.presheaf.map k.op (γloc Z g hg)) ?_).symm
    obtain ⟨i₀, c₀, hc₀⟩ := (Sieve.mem_ofArrows_iff V f (g ≫ Y.unop.hom)).1 hg
    have hc₁ : (k ≫ g) ≫ Y.unop.hom = (k ≫ c₀) ≫ f i₀ := by simp [hc₀]
    refine glued_smul_of_smul D Y G H Z' (k ≫ g) _ i₀ (k ≫ c₀) hc₁ ?_
    rw [← G.sec_restrict i₀ Z Z' k g c₀ hc₀ hc₁, ← H.sec_restrict i₀ Z Z' k g c₀ hc₀ hc₁,
      ← (D.x i₀).totalMap_totalSmul k.op (γloc Z g hg) (G.sec i₀ Z g c₀ hc₀),
      hγloc₁ Z g hg i₀ c₀ hc₀])
  obtain ⟨γ, hγam, hγuniq⟩ := hex
  refine ⟨γ, ?_, ?_⟩
  · refine Glued.ext' D fun i Z g c h => ?_
    have hg : ((Sieve.ofArrows V f).pullback Y.unop.hom) g :=
      (Sieve.mem_ofArrows_iff V f (g ≫ Y.unop.hom)).2 ⟨i, c, h⟩
    refine Eq.trans (congrArg (fun z => (D.x i).totalSmul z (G.sec i Z g c h))
      (hγam g hg)) ?_
    exact hγloc₁ Z g hg i c h
  · intro δ hδ
    refine hγuniq δ ?_
    intro Z g hg
    refine hγloc₂ Z g hg (𝒢.presheaf.map g.op δ) ?_
    intro i c h
    exact congrArg (fun A : Glued D Y.unop.hom => A.sec i Z g c h) hδ

/-- **The torsor glued from a descent datum**, as a pseudo-torsor under the restriction of `𝒢`
to the localized site `C/U`. -/
def gluedPseudoTorsor (hf : Sieve.ofArrows V f ∈ J U) :
    PseudoTorsor.{max u v s t} (𝒢.over U) where
  presheaf := gluedPresheaf D
  isSheaf := gluedPresheaf_isSheaf D
  act := gluedAct D
  one_act Y G := Glued.ext' D fun i Z g c h =>
    (congrArg (fun z => (D.x i).totalSmul z (G.sec i Z g c h))
        (SheafOfGroups.map_one (G := 𝒢) g.op)).trans
      (totalSmul_one (D.x i) (G.sec i Z g c h))
  mul_act Y γ δ G := Glued.ext' D fun i Z g c h =>
    (congrArg (fun z => (D.x i).totalSmul z (G.sec i Z g c h)) (𝒢.map_mul g.op γ δ)).trans
      (totalSmul_mul (D.x i) _ _ (G.sec i Z g c h))
  naturality := fun {Y₁ Y₂} k γ G => Glued.ext' D fun i Z g c h => by
    have h' : (g ≫ k.unop.left) ≫ Y₁.unop.hom = c ≫ f i := by
      rw [Category.assoc, Over.w k.unop]
      exact h
    exact congrArg (fun z => (D.x i).totalSmul z (G.sec i Z (g ≫ k.unop.left) c h'))
      (𝒢.presheaf.map_comp_apply k.unop.left.op g.op γ)
  simplyTransitive Y _ G H := glued_simplyTransitive D hf Y G H

/-- The sieve of morphisms over which the presheaf glued from a descent datum has a section. -/
def nonemptySieve {W : C} (β : W ⟶ U) : Sieve W where
  arrows Z g := Nonempty (Glued D (g ≫ β))
  downward_closed := fun hg k => hg.elim fun G => ⟨Glued.restrict D G k (by simp)⟩

/-- **The presheaf glued from a descent datum is locally nonempty.** Every morphism to `U`
factors, locally on a covering, through a member of the covering family in such a way that the
corresponding `D.x i` has a section there, and such a section spreads out to a matching
family. -/
theorem nonemptySieve_mem (hf : Sieve.ofArrows V f ∈ J U) {W : C} (β : W ⟶ U) :
    nonemptySieve D β ∈ J W := by
  refine J.transitive (J.pullback_stable β hf) (nonemptySieve D β) ?_
  intro Z g hg
  obtain ⟨i, c, hc⟩ := (Sieve.mem_ofArrows_iff V f (g ≫ β)).1 hg
  obtain ⟨S', hS', hsec⟩ := (D.x i).isTorsor (Over.mk (c ≫ eqToHom (base_x D i).symm))
  refine J.superset_covering ?_ ((J.mem_over_iff S').1 hS')
  intro Z' k hk
  obtain ⟨σ⟩ := hsec ((Sieve.overEquiv_iff S' k).1 hk)
  obtain ⟨G, -, -⟩ := exists_glued D i Z' (k ≫ c)
    (⟨k ≫ (c ≫ eqToHom (base_x D i).symm), σ⟩ : (D.x i).Total (op Z'))
    (Category.assoc k c (eqToHom (base_x D i).symm)).symm
  have he : (k ≫ c) ≫ f i = (k ≫ g) ≫ β := by
    rw [Category.assoc, ← hc, Category.assoc]
  exact ⟨he ▸ G⟩

/-- **The object of `𝒢-Torsors` glued from a descent datum**: the torsor on `C/U` whose sections
are the matching families of `SheafOfGroups.Torsors.Descent.Glued`, lying over `U`. -/
@[implicit_reducible]
def gluedTorsorObj (hf : Sieve.ofArrows V f ∈ J U) : Torsors.{max u v s t} 𝒢 where
  base := U
  torsor := gluedPseudoTorsor D hf
  isTorsor := fun Y => ⟨(Sieve.overEquiv Y).symm (nonemptySieve D Y.hom),
    J.overEquiv_symm_mem_over Y _ (nonemptySieve_mem D hf Y.hom), by
      intro Y' u hu
      have hu' : Nonempty (Glued D (u.left ≫ Y.hom)) := hu
      obtain ⟨G⟩ := hu'
      exact ⟨cast (congrArg (fun z : Y'.left ⟶ U => Glued D z) (Over.w u)) G⟩⟩

end Descent

namespace Descent

variable {U : C} {I : Type s} {V : I → C} {f : ∀ i, V i ⟶ U}
  {Vij : I → I → C} {pr₁ : ∀ i j, Vij i j ⟶ V i} {pr₂ : ∀ i j, Vij i j ⟶ V j}
  {hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j)}
  {Vijk : I → I → I → C}
  {s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j} {s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k}
  {hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k)}
  {q₁ : ∀ i j k, Vijk i j k ⟶ V i} {q₂ : ∀ i j k, Vijk i j k ⟶ V j}
  {q₃ : ∀ i j k, Vijk i j k ⟶ V k}
  {hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j}
  {hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j}
  {hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k}
  (D : Functor.DescentDatum (projection : Torsors.{t} 𝒢 ⥤ C) V f Vij pr₁ pr₂ hVij
    Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃)

/-- **Being the matching family spread out from a section of a member of the descent datum.**
The section `G` of the glued sheaf over `β` is spread out from the element `p` of the total space
of `D.x i` over `Z` along the factorization `β = c ≫ f i` when it attaches `p` to the identity
factorization. -/
def IsSpread (i : I) (Z : C) (c : Z ⟶ V i) (p : (D.x i).Total (op Z)) {β : Z ⟶ U}
    (G : Glued D β) : Prop :=
  β = c ≫ f i ∧ ∀ h : 𝟙 Z ≫ β = c ≫ f i, G.sec i Z (𝟙 Z) c h = p

/-- Every element of the total space of `D.x i` lying over `c` spreads out to a section of the
glued sheaf over any morphism equal to `c ≫ f i`. -/
theorem exists_isSpread (i : I) (Z : C) (c : Z ⟶ V i) (p : (D.x i).Total (op Z))
    (hp : p.1 = c ≫ eqToHom (base_x D i).symm) {β : Z ⟶ U} (hβ : β = c ≫ f i) :
    ∃ G : Glued D β, IsSpread D i Z c p G := by
  subst hβ
  obtain ⟨G, hG, -⟩ := exists_glued D i Z c p hp
  exact ⟨G, rfl, fun _ => hG⟩

/-- Two sections of the glued sheaf spread out from the same element attach the same elements to
the same factorizations. -/
theorem isSpread_sec_eq (i : I) (Z : C) (c : Z ⟶ V i) (p : (D.x i).Total (op Z))
    {β β' : Z ⟶ U} (G : Glued D β) (G' : Glued D β')
    (hG : IsSpread D i Z c p G) (hG' : IsSpread D i Z c p G')
    (l : I) (Z' : C) (g : Z' ⟶ Z) (d : Z' ⟶ V l) (h : g ≫ β = d ≫ f l)
    (h' : g ≫ β' = d ≫ f l) : G.sec l Z' g d h = G'.sec l Z' g d h' := by
  obtain ⟨hβ, hG⟩ := hG
  obtain ⟨hβ', hG'⟩ := hG'
  subst hβ
  subst hβ'
  obtain ⟨e, he₁, he₂⟩ := exists_overlapLift (hVij i l) (g ≫ c) d
    ((Category.assoc g c (f i)).trans h)
  have hA := glued_sec_eq_transition D i l Z Z' c G g d h e he₁ he₂
  have hB := glued_sec_eq_transition D i l Z Z' c G' g d h' e he₁ he₂
  rw [hG (Category.id_comp _)] at hA
  rw [hG' (Category.id_comp _)] at hB
  exact IsTransition.unique D hA hB

/-- The restriction of a spread section of the glued sheaf is the spread of the restricted
element. -/
theorem isSpread_restrict (i : I) (Z Z' : C) (c : Z ⟶ V i) (p : (D.x i).Total (op Z))
    {β : Z ⟶ U} (G : Glued D β) (hG : IsSpread D i Z c p G) (k : Z' ⟶ Z) {β' : Z' ⟶ U}
    (hk : k ≫ β = β') :
    IsSpread D i Z' (k ≫ c) ((D.x i).totalMap k.op p) (Glued.restrict D G k hk) := by
  obtain ⟨hβ, hG⟩ := hG
  subst hβ
  subst hk
  refine ⟨(Category.assoc k c (f i)).symm, fun h => ?_⟩
  have hX : (k ≫ 𝟙 Z) ≫ (c ≫ f i) = (k ≫ c) ≫ f i := by simp
  have h'' : (𝟙 Z' ≫ k) ≫ (c ≫ f i) = (k ≫ c) ≫ f i := by simp
  refine Eq.trans (Glued.restrict_sec D G k rfl i Z' (𝟙 Z') (k ≫ c) h h'') ?_
  refine Eq.trans (Glued.sec_congr D G i Z'
    ((Category.id_comp k).trans (Category.comp_id k).symm) rfl h'' hX) ?_
  refine Eq.trans (G.sec_restrict i Z Z' k (𝟙 Z) c (Category.id_comp _) hX).symm ?_
  exact congrArg ((D.x i).totalMap k.op) (hG (Category.id_comp _))

/-- The action of `𝒢` on a spread section of the glued sheaf is the spread of the element acted
on. -/
theorem isSpread_smul (i : I) (Z : C) (c : Z ⟶ V i) (p : (D.x i).Total (op Z)) {β : Z ⟶ U}
    (G : Glued D β) (hG : IsSpread D i Z c p G) (γ : 𝒢.presheaf.obj (op Z)) :
    IsSpread D i Z c ((D.x i).totalSmul γ p) (gluedAct D (op (Over.mk β)) γ G) := by
  obtain ⟨hβ, hG⟩ := hG
  refine ⟨hβ, fun h => ?_⟩
  refine Eq.trans (congrArg (fun z => (D.x i).totalSmul z (G.sec i Z (𝟙 Z) c h))
    (𝒢.presheaf.map_id_apply (op Z) γ)) ?_
  exact congrArg ((D.x i).totalSmul γ) (hG h)

/-- Being spread out depends only on the factorization and the element, not on the proofs. -/
theorem isSpread_congr (i : I) (Z : C) {c c' : Z ⟶ V i} (hc : c = c')
    {p p' : (D.x i).Total (op Z)} (hp : p = p') {β : Z ⟶ U} (G : Glued D β)
    (hG : IsSpread D i Z c p G) : IsSpread D i Z c' p' G := by
  subst hc
  subst hp
  exact hG

/-- **Two elements of the total spaces of two members of the descent datum which are in
transition spread out to the same section of the glued sheaf.** -/
theorem isSpread_sec_eq_of_transition (i j : I) (Z : C) (e : Z ⟶ Vij i j)
    (p : (D.x i).Total (op Z)) (q : (D.x j).Total (op Z)) (hpq : IsTransition D i j Z e p q)
    {β β' : Z ⟶ U} (G : Glued D β) (H : Glued D β')
    (hG : IsSpread D i Z (e ≫ pr₁ i j) p G) (hH : IsSpread D j Z (e ≫ pr₂ i j) q H)
    (l : I) (Z' : C) (g : Z' ⟶ Z) (d : Z' ⟶ V l) (h₁ : g ≫ β = d ≫ f l)
    (h₂ : g ≫ β' = d ≫ f l) : G.sec l Z' g d h₁ = H.sec l Z' g d h₂ := by
  obtain ⟨hβ, hG⟩ := hG
  obtain ⟨hβ', hH⟩ := hH
  subst hβ
  subst hβ'
  exact glued_sec_eq_of_transition D i j Z e p q hpq G H (hG (Category.id_comp _))
    (hH (Category.id_comp _)) l Z' g d h₁ h₂

end Descent

namespace Descent

variable {U : C} {I : Type s} {V : I → C} {f : ∀ i, V i ⟶ U}
  {Vij : I → I → C} {pr₁ : ∀ i j, Vij i j ⟶ V i} {pr₂ : ∀ i j, Vij i j ⟶ V j}
  {hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j)}
  {Vijk : I → I → I → C}
  {s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j} {s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k}
  {hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k)}
  {q₁ : ∀ i j k, Vijk i j k ⟶ V i} {q₂ : ∀ i j k, Vijk i j k ⟶ V j}
  {q₃ : ∀ i j k, Vijk i j k ⟶ V k}
  {hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j}
  {hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j}
  {hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k}
  (D : Functor.DescentDatum (projection : Torsors.{t} 𝒢 ⥤ C) V f Vij pr₁ pr₂ hVij
    Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃)

/-- Two elements of the total space of the glued torsor with the same base component whose
matching families attach the same elements to the same factorizations are equal. -/
theorem total_gluedTorsorObj_ext (hf : Sieve.ofArrows V f ∈ J U) {Z : Cᵒᵖ}
    (r r' : (gluedTorsorObj D hf).Total Z) (h₁ : r.1 = r'.1)
    (h₂ : ∀ (l : I) (Z' : C) (g : Z' ⟶ Z.unop) (c : Z' ⟶ V l)
      (h : g ≫ r.1 = c ≫ f l) (h' : g ≫ r'.1 = c ≫ f l),
      r.2.sec l Z' g c h = r'.2.sec l Z' g c h') : r = r' := by
  obtain ⟨a, G⟩ := r
  obtain ⟨b, H⟩ := r'
  obtain rfl : a = b := h₁
  exact congrArg (fun z => (⟨a, z⟩ : (gluedTorsorObj D hf).Total Z))
    (Glued.ext' D fun l Z' g c hc => h₂ l Z' g c hc hc)

/-- Equal elements of the total space of the glued torsor have matching families attaching the
same elements to the same factorizations. -/
theorem total_gluedTorsorObj_sec_eq (hf : Sieve.ofArrows V f ∈ J U) {Z : Cᵒᵖ}
    {r r' : (gluedTorsorObj D hf).Total Z} (hrr' : r = r') (l : I) (Z' : C) (g : Z' ⟶ Z.unop)
    (c : Z' ⟶ V l) (h : g ≫ r.1 = c ≫ f l) (h' : g ≫ r'.1 = c ≫ f l) :
    r.2.sec l Z' g c h = r'.2.sec l Z' g c h' := by
  subst hrr'
  rfl

end Descent

/-- **Stacks 04UK**, condition (3) of Stacks 02ZI: every descent datum for
`p : 𝒢-Torsors ⥤ C` relative to a `J`-covering family with genuine fibre-product overlaps is
effective.

The object over `U` is glued by hand: the sections of its torsor over `(W, β)` are the matching
families which assign, to every factorization of `g ≫ β` through a member `f i` of the covering
family, a section of `D.x i`, compatibly with the restriction maps and with the glueing
isomorphisms of the descent datum. That this is a sheaf is the sheaf condition for the `D.x i`;
that `𝒢` acts simply transitively on it is the simple transitivity on the `D.x i` together with
the sheaf condition for `𝒢`; and that it is locally nonempty follows because each `D.x i` is.
The morphisms `D.x i ⟶ x` send a section of `D.x i` to the matching family it spreads out to,
whose compatibility over the double overlaps is exactly the cocycle condition of the descent
datum, and which recovers the section it came from because of the cocycle condition at
`(i, i, i)`. Effectivity then follows from
`SheafOfGroups.Torsors.isEffective_of_glueing`.

A matching family is indexed by the objects and the morphisms of `C` and by the index set of the
covering family, so it lives in `Type (max u v s t)`: the statement is for torsors whose
sections lie in `Type (max u v s t)`, which is the same bound `max u v s ≤ t` that the route
through Stacks 04TP and 04TS imposes. -/
@[stacks 04UK "condition (3): descent data are effective", ega "IV 16.5.15" "more general"]
theorem projection_effectiveDescent {U : C} {I : Type s} (V : I → C) (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ J U)
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
    (D : Functor.DescentDatum (projection : Torsors.{max u v s t} 𝒢 ⥤ C) V f Vij pr₁ pr₂ hVij
      Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃) :
    D.IsEffective := by
  have hspread : ∀ (i : I) (Z : Cᵒᵖ) (p : (D.x i).Total Z),
      ∃ G : Descent.Glued D (p.1 ≫ (eqToHom (Descent.base_x D i) ≫ f i)),
        Descent.IsSpread D i Z.unop (p.1 ≫ eqToHom (Descent.base_x D i)) p G :=
    fun i Z p => Descent.exists_isSpread D i Z.unop (p.1 ≫ eqToHom (Descent.base_x D i)) p
      (by simp) (Category.assoc _ _ _).symm
  choose Sp hSp using hspread
  have hsp : ∀ (i : I) (Z : Cᵒᵖ) (p : (D.x i).Total Z) (a : Z.unop ⟶ (D.x i).base), p.1 = a →
      Descent.IsSpread D i Z.unop (a ≫ eqToHom (Descent.base_x D i)) p (Sp i Z p) :=
    fun i Z p a hpa => Descent.isSpread_congr D i Z.unop
      (congrArg (fun z => z ≫ eqToHom (Descent.base_x D i)) hpa) rfl _ (hSp i Z p)
  have hchi : ∀ i : I, ∃ χ : D.x i ⟶ Descent.gluedTorsorObj D hf,
      Hom.base χ = eqToHom (Descent.base_x D i) ≫ f i ∧
      ∀ (Z : Cᵒᵖ) (p : (D.x i).Total Z),
        χ.map Z p = ⟨p.1 ≫ (eqToHom (Descent.base_x D i) ≫ f i), Sp i Z p⟩ := by
    intro i
    refine ⟨⟨eqToHom (Descent.base_x D i) ≫ f i,
      fun Z p => ⟨p.1 ≫ (eqToHom (Descent.base_x D i) ≫ f i), Sp i Z p⟩, ?_, ?_, ?_⟩,
      rfl, fun Z p => rfl⟩
    · intro Z Z' h p
      refine Descent.total_gluedTorsorObj_ext D hf _ _
        (Category.assoc h.unop p.1 (eqToHom (Descent.base_x D i) ≫ f i)) ?_
      intro l Z'' g c hh hh'
      exact Descent.isSpread_sec_eq D i Z'.unop
        (((D.x i).totalMap h p).1 ≫ eqToHom (Descent.base_x D i)) ((D.x i).totalMap h p) _ _
        (hSp i Z' ((D.x i).totalMap h p))
        (Descent.isSpread_congr D i Z'.unop
          (Category.assoc h.unop p.1 (eqToHom (Descent.base_x D i))).symm rfl _
          (Descent.isSpread_restrict D i Z.unop Z'.unop
            (p.1 ≫ eqToHom (Descent.base_x D i)) p (Sp i Z p) (hSp i Z p) h.unop rfl))
        l Z'' g c hh hh'
    · intro Z γ p
      refine Descent.total_gluedTorsorObj_ext D hf _ _ rfl ?_
      intro l Z'' g c hh hh'
      exact Descent.isSpread_sec_eq D i Z.unop (p.1 ≫ eqToHom (Descent.base_x D i))
        ((D.x i).totalSmul γ p) _ _ (hSp i Z ((D.x i).totalSmul γ p))
        (Descent.isSpread_smul D i Z.unop (p.1 ≫ eqToHom (Descent.base_x D i)) p (Sp i Z p)
          (hSp i Z p) γ) l Z'' g c hh hh'
    · intro Z a
      refine ⟨fun p hp => ?_, fun p hp p' hp' hpp' => ?_, fun q hq => ?_⟩
      · have hpa : p.1 = a := hp
        exact show p.1 ≫ _ = a ≫ _ by rw [hpa]
      · have hpa : p.1 = a := hp
        have hpa' : p'.1 = a := hp'
        have hh : 𝟙 Z.unop ≫ (p.1 ≫ (eqToHom (Descent.base_x D i) ≫ f i)) =
            (a ≫ eqToHom (Descent.base_x D i)) ≫ f i := by
          rw [Category.id_comp, hpa, Category.assoc]
        have hh' : 𝟙 Z.unop ≫ (p'.1 ≫ (eqToHom (Descent.base_x D i) ≫ f i)) =
            (a ≫ eqToHom (Descent.base_x D i)) ≫ f i := by
          rw [Category.id_comp, hpa', Category.assoc]
        have hkey := Descent.total_gluedTorsorObj_sec_eq D hf hpp' i Z.unop (𝟙 Z.unop)
          (a ≫ eqToHom (Descent.base_x D i)) hh hh'
        exact ((hsp i Z p a hpa).2 hh).symm.trans (hkey.trans ((hsp i Z p' a hpa').2 hh'))
      · have hqa : q.1 = a ≫ (eqToHom (Descent.base_x D i) ≫ f i) := hq
        have hh : 𝟙 Z.unop ≫ q.1 = (a ≫ eqToHom (Descent.base_x D i)) ≫ f i := by
          rw [Category.id_comp, hqa, Category.assoc]
        have hqβ : q.1 = (a ≫ eqToHom (Descent.base_x D i)) ≫ f i := by
          rw [hqa, Category.assoc]
        have hp₁ : (q.2.sec i Z.unop (𝟙 Z.unop)
            (a ≫ eqToHom (Descent.base_x D i)) hh).1 = a :=
          (q.2.base_sec i Z.unop (𝟙 Z.unop) (a ≫ eqToHom (Descent.base_x D i)) hh).trans
            (by simp)
        refine ⟨q.2.sec i Z.unop (𝟙 Z.unop) (a ≫ eqToHom (Descent.base_x D i)) hh, hp₁, ?_⟩
        refine Descent.total_gluedTorsorObj_ext D hf _ _
          ((congrArg (fun z => z ≫ (eqToHom (Descent.base_x D i) ≫ f i)) hp₁).trans
            hqa.symm) ?_
        intro l Z'' g c hh₁ hh₂
        exact Descent.isSpread_sec_eq D i Z.unop (a ≫ eqToHom (Descent.base_x D i)) _ _ _
          (hsp i Z _ a hp₁)
          ⟨hqβ, fun _ => rfl⟩ l Z'' g c hh₁ hh₂
  choose χ hχb hχmap using hchi
  refine isEffective_of_glueing V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃
    D (Descent.gluedTorsorObj D hf) rfl χ
    (fun i => isHomLift_of_base (χ i) ((hχb i).trans
      (congrArg (fun z => eqToHom (Descent.base_x D i) ≫ z)
        (Category.comp_id (f i)).symm))) ?_
  intro i j
  refine Hom.ext ?_ (funext fun Z => funext fun r => ?_)
  · change Hom.base (D.φ i j) ≫ Hom.base (D.xrji i j).hom ≫ Hom.base (χ j) =
      Hom.base (D.xrij i j).hom ≫ Hom.base (χ i)
    rw [Descent.homBase_phi, Descent.homBase_xrji, Descent.homBase_xrij, hχb i, hχb j]
    simp [(hVij i j).w]
  · have hptr : Descent.IsTransition D i j Z.unop (r.1 ≫ eqToHom (Descent.base_xrij D i j))
        ((D.xrij i j).hom.map Z r) ((D.φ i j ≫ (D.xrji i j).hom).map Z r) :=
      ⟨r, by simp, rfl, rfl⟩
    have hbi : ((D.xrij i j).hom.map Z r).1 ≫ eqToHom (Descent.base_x D i) =
        (r.1 ≫ eqToHom (Descent.base_xrij D i j)) ≫ pr₁ i j := by
      rw [Hom.fst_map, Descent.homBase_xrij]
      simp
    have hbj : ((D.φ i j ≫ (D.xrji i j).hom).map Z r).1 ≫ eqToHom (Descent.base_x D j) =
        (r.1 ≫ eqToHom (Descent.base_xrij D i j)) ≫ pr₂ i j := by
      rw [Hom.fst_map, Descent.homBase_glue]
      simp
    change (χ j).map Z ((D.φ i j ≫ (D.xrji i j).hom).map Z r) =
      (χ i).map Z ((D.xrij i j).hom.map Z r)
    rw [hχmap j Z _, hχmap i Z _]
    refine Descent.total_gluedTorsorObj_ext D hf _ _ ?_ ?_
    · have e₁ : (((D.φ i j ≫ (D.xrji i j).hom).map Z r).1 ≫
            eqToHom (Descent.base_x D j)) ≫ f j =
          (((D.xrij i j).hom.map Z r).1 ≫ eqToHom (Descent.base_x D i)) ≫ f i := by
        rw [hbj, hbi]
        simp only [Category.assoc]
        rw [(hVij i j).w]
      exact (Category.assoc _ _ _).symm.trans (e₁.trans (Category.assoc _ _ _))
    · intro l Z'' g c hh₁ hh₂
      exact (Descent.isSpread_sec_eq_of_transition D i j Z.unop
        (r.1 ≫ eqToHom (Descent.base_xrij D i j)) _ _ hptr _ _
        (Descent.isSpread_congr D i Z.unop hbi rfl _ (hSp i Z _))
        (Descent.isSpread_congr D j Z.unop hbj rfl _ (hSp j Z _))
        l Z'' g c hh₂ hh₁).symm

/-- **Stacks 04UK.** The functor `p : 𝒢-Torsors ⥤ C` of Stacks 04UJ is a stack in groupoids
over the site `(C, J)`: it is fibred in groupoids, its `Isom` presheaves are sheaves, and every
descent datum relative to a covering family is effective. -/
@[stacks 04UK, sga "3 IV 4.5.13" "special case"]
theorem projection_isStackInGroupoids :
    Functor.IsStackInGroupoids.{s} (projection : Torsors.{max u v s t} 𝒢 ⥤ C) J where
  isFiberedInGroupoids := projection_isFiberedInGroupoids
  isom_isSheaf := by
    intro W x y hx hy I V f hf Vij pr₁ pr₂ hVij xr yr xrij yrij
    exact projection_isomIsSheaf x y hx hy V f hf Vij pr₁ pr₂ hVij xr yr xrij yrij
  effective_descent := by
    intro W I V f hf Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃ D
    exact projection_effectiveDescent.{t, w, v, u, s} V f hf Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃
      hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃ D

end SheafOfGroups.Torsors

end
