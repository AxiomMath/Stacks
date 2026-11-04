module

public import StacksFrontier.AlgebraicGeometry.Stacks.CartesianKernelFlat

/-!
# A global presentation of a restriction, from sections over the image of a terminal object

Let `Fn : C' ⥤ C` be a continuous functor, `t` a terminal object of `C'` and `M` a sheaf of
modules on `C`. The restriction of `M` along `Fn`, read over a sheaf of rings equal to the
restriction of the ring of `M`, has a global presentation as soon as there are sections `s i` of
`M` over `Fn t` which generate the sections over every `Fn V` locally on `V`, and relations
`ρ k` among them which generate all relations locally on `V`. Locally may be read on a covering
*presieve*: the restriction to the generated sieve is automatic.

This is `Stacks.SheafOfModules.FreeSheafification.isPresentedByGlobalSections_of_terminal`
(Stacks 03DE (6)) read along `Fn`; the equality of rings is eliminated before the sections are
compared, so all the algebra takes place in the sections of `M` and the ring of `M` themselves.

## Main results

* `Stacks.SheafOfModules.FreeSheafification.isPresentedByGlobalSections_of_terminal_ofPresieve`.
* `Stacks.SheafOfModules.FreeSheafification.isPresentedByGlobalSections_pushforward_of_terminal`.

## References

* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u u'

namespace Stacks.SheafOfModules.FreeSheafification

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (t : C) (ht : IsTerminal t) (N : _root_.SheafOfModules.{u} R)

/-- **`isPresentedByGlobalSections_of_terminal` with its two local conditions read on covering
presieves.** -/
theorem isPresentedByGlobalSections_of_terminal_ofPresieve (I K : Type u)
    (s : I → N.val.obj (op t))
    (ρ : K → I →₀ R.obj.obj (op t)) (hρ : ∀ k, ((ρ k).sum fun i r ↦ r • s i) = 0)
    (hgen : ∀ (V : C) (x : N.val.obj (op V)), ∃ T : Presieve V, Sieve.generate T ∈ J V ∧
      ∀ ⦃B : C⦄ (g : B ⟶ V), T g → ∃ c : I →₀ R.obj.obj (op B),
        (c.sum fun i r ↦ r • (show N.val.obj (op B) from N.val.map (ht.from B).op (s i))) =
          N.val.map g.op x)
    (hrel : ∀ (V : C) (c : I →₀ R.obj.obj (op V)),
      (c.sum fun i r ↦ r • (show N.val.obj (op V) from N.val.map (ht.from V).op (s i))) = 0 →
      ∃ T : Presieve V, Sieve.generate T ∈ J V ∧ ∀ ⦃B : C⦄ (g : B ⟶ V), T g →
        ∃ d : K →₀ R.obj.obj (op B), c.mapRange (R.obj.map g.op).hom (map_zero _) =
          d.sum fun k r ↦ r • (ρ k).mapRange (R.obj.map (ht.from B).op).hom (map_zero _)) :
    N.IsPresentedByGlobalSections ∧
      (Finite I → Finite K → N.IsFinitelyPresentedByGlobalSections) := by
  classical
  refine isPresentedByGlobalSections_of_terminal t ht N I K s ρ hρ (fun V x ↦ ?_) (fun V c hc ↦ ?_)
  · obtain ⟨T, hT, hx⟩ := hgen V x
    refine ⟨Sieve.generate T, hT, ?_⟩
    rintro B _ ⟨B', e, g, hg, rfl⟩
    obtain ⟨c, hc⟩ := hx g hg
    refine ⟨c.mapRange (R.obj.map e.op).hom (map_zero _), Eq.trans ?_
      ((congrArg (N.val.map e.op) hc).trans (N.val.map_comp_apply g.op e.op x).symm)⟩
    refine Eq.trans ?_ (map_finsupp_sum_smul N.val e.op c
      (fun i ↦ (show N.val.obj (op B') from N.val.map (ht.from B').op (s i)))).symm
    refine Finset.sum_congr rfl fun i _ ↦ congrArg (_ • ·) ?_
    exact (N.val.congr_map_apply (congrArg Quiver.Hom.op (ht.hom_ext (ht.from B)
      (e ≫ ht.from B'))) (s i)).trans (N.val.map_comp_apply (ht.from B').op e.op (s i))
  · obtain ⟨T, hT, hx⟩ := hrel V c hc
    refine ⟨Sieve.generate T, hT, ?_⟩
    rintro B _ ⟨B', e, g, hg, rfl⟩
    obtain ⟨d, hd⟩ := hx g hg
    refine ⟨d.mapRange (R.obj.map e.op).hom (map_zero _), ?_⟩
    have hcomp : c.mapRange (R.obj.map (e ≫ g).op).hom (map_zero _) =
        (c.mapRange (R.obj.map g.op).hom (map_zero _)).mapRange (R.obj.map e.op).hom
          (map_zero _) := by
      ext i
      simp [Functor.map_comp]
    rw [hcomp, hd, Finsupp.mapRange_sum_smul (R.obj.map e.op).hom]
    refine Finset.sum_congr rfl fun k _ ↦ congrArg (_ • ·) ?_
    ext i
    simp only [Finsupp.mapRange_apply]
    rw [← RingCat.comp_apply, ← Functor.map_comp, ← op_comp,
      ht.hom_ext (e ≫ ht.from B') (ht.from B)]

variable {C' : Type*} [Category C'] {J' : GrothendieckTopology C'}
  [HasSheafify J' AddCommGrpCat.{u}] [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (Fn : C' ⥤ C) [Fn.IsContinuous J' J] {R' : Sheaf J' RingCat.{u}}

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **A global presentation of the restriction of `M` along `Fn`**, from sections of `M` over the
image of a terminal object generating locally and relations generating all relations locally;
everything is read in the sections and the ring of `M` at the images of the objects of `C'`. -/
theorem isPresentedByGlobalSections_pushforward_of_terminal
    (h : (Fn.sheafPushforwardContinuous RingCat.{u} J' J).obj R = R')
    (M : _root_.SheafOfModules.{u} R) (t : C') (ht : IsTerminal t) (I K : Type u)
    (s : I → M.val.obj (op (Fn.obj t)))
    (ρ : K → I →₀ R.obj.obj (op (Fn.obj t))) (hρ : ∀ k, ((ρ k).sum fun i r ↦ r • s i) = 0)
    (hgen : ∀ (V : C') (x : M.val.obj (op (Fn.obj V))), ∃ T : Presieve V,
      Sieve.generate T ∈ J' V ∧ ∀ ⦃B : C'⦄ (g : B ⟶ V), T g →
        ∃ c : I →₀ R.obj.obj (op (Fn.obj B)),
          (c.sum fun i r ↦ r • (show M.val.obj (op (Fn.obj B)) from
            M.val.map (Fn.map (ht.from B)).op (s i))) = M.val.map (Fn.map g).op x)
    (hrel : ∀ (V : C') (c : I →₀ R.obj.obj (op (Fn.obj V))),
      (c.sum fun i r ↦ r • (show M.val.obj (op (Fn.obj V)) from
        M.val.map (Fn.map (ht.from V)).op (s i))) = 0 →
      ∃ T : Presieve V, Sieve.generate T ∈ J' V ∧ ∀ ⦃B : C'⦄ (g : B ⟶ V), T g →
        ∃ d : K →₀ R.obj.obj (op (Fn.obj B)),
          c.mapRange (R.obj.map (Fn.map g).op).hom (map_zero _) =
            d.sum fun k r ↦ r • (ρ k).mapRange (R.obj.map (Fn.map (ht.from B)).op).hom
              (map_zero _)) :
    ((_root_.SheafOfModules.pushforward.{u} (F := Fn) (eqToHom h.symm)).obj
        M).IsPresentedByGlobalSections ∧
      (Finite I → Finite K → ((_root_.SheafOfModules.pushforward.{u} (F := Fn)
        (eqToHom h.symm)).obj M).IsFinitelyPresentedByGlobalSections) := by
  subst h
  exact isPresentedByGlobalSections_of_terminal_ofPresieve t ht
    ((_root_.SheafOfModules.pushforward.{u} (F := Fn) (𝟙 _)).obj M) I K s ρ hρ hgen hrel

end Stacks.SheafOfModules.FreeSheafification

end
