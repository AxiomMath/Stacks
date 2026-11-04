module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleStrictTransitionComparison
public meta import StacksFrontier.Tactic.HEqCongr

/-!
# The transition coherence of the strict system of a derived pullback

Let `X` be a simplicial algebraic space with an augmentation `a : X → Z`, `b` the augmentation on
the strict total site, `g_n` the component morphisms, `realize_n` the realization equivalences and
`f_φ` the transition morphisms of the strict components. For `K` in `D(Z)` the derived transition
of Stacks 0D9P of the system of `Lb^*K` along `φ : [m] ⟶ [n]`, read through the component
isomorphisms `Lb^* ⋙ D(g_n^{-1}) ⋙ L realize_n^* ≅ La_n^*`, is the derived square of the strict
transitions followed by `La_m^* ⋙ LX(φ)^* ≅ La_n^*`.

## Main results

* `CategoryTheory.transition_transport_comparison_of_squares`: the abstract form, a transition
  read through componentwise comparisons assembled from three squares.
* `CategoryTheory.transition_homotopy_of_degreewise`: the upstairs identity from a degreewise one.
* `strictAugmentationDegreeDerivedIso_transition_of_homotopy` and its componentwise form
  `strictAugmentationDegreeDerivedIso_transition_app_of_homotopy`, in the namespace
  `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite`: the coherence, from its form on complexes
  `StrictTransitionHomotopyIdentity`.

## References

* [Stacks Project, Tag 0D9P](https://stacks.math.columbia.edu/tag/0D9P)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite CategoryTheory.Limits AlgebraicGeometry.RingedToposHom

namespace CategoryTheory

universe v₀ v₁ v₂ v₃ v₄ v₅ v₆ w₀ w₁ w₂ w₃ w₄ w₅ w₆ u₀ u₁ u₂ u₃ u₄ u₅ u₆ t₀ t₁ t₂ t₃ t₄ t₅ t₆

/-- The upstairs identity of `CategoryTheory.transition_transport_comparison_of_squares`: the
transition `τ` read through the composites `σ₀⁻¹ ≫ d ε₀ ≫ ν₀` is `β₀` followed by `x` of the
composite in degree `m` and by `θ₀`. -/
structure TransitionHomotopyIdentity {H₀ : Type u₀} {H₁ : Type u₁} {H₂ : Type u₂}
    {H₃ : Type u₃} {H₄ : Type u₄} {H₅ : Type u₅} {H₆ : Type u₆} [Category.{v₀} H₀]
    [Category.{v₁} H₁] [Category.{v₂} H₂] [Category.{v₃} H₃] [Category.{v₄} H₄]
    [Category.{v₅} H₅] [Category.{v₆} H₆]
    {b : H₀ ⥤ H₁} {rm : H₁ ⥤ H₂} {rn : H₁ ⥤ H₃} {f : H₂ ⥤ H₃} {sn : H₃ ⥤ H₅}
    {sm : H₂ ⥤ H₄} {x : H₄ ⥤ H₅} {am : H₀ ⥤ H₄} {an : H₀ ⥤ H₅}
    {e : H₁ ⥤ H₆} {a : H₀ ⥤ H₆} {dn : H₆ ⥤ H₅} {dm : H₆ ⥤ H₄}
    (τ : rm ⋙ f ⟶ rn) (σ₀n : e ⋙ dn ≅ rn ⋙ sn) (σ₀m : e ⋙ dm ≅ rm ⋙ sm) (ε₀ : b ⋙ e ⟶ a)
    (ν₀n : a ⋙ dn ⟶ an) (ν₀m : a ⋙ dm ⟶ am) (β₀ : f ⋙ sn ⟶ sm ⋙ x) (θ₀ : am ⋙ x ⟶ an) :
    Prop where
  eq : ∀ M, sn.map (τ.app (b.obj M)) ≫ σ₀n.inv.app (b.obj M) ≫ dn.map (ε₀.app M) ≫
      ν₀n.app M =
    β₀.app (rm.obj (b.obj M)) ≫
      x.map (σ₀m.inv.app (b.obj M) ≫ dm.map (ε₀.app M) ≫ ν₀m.app M) ≫ θ₀.app M

/-- **A transition read through componentwise comparisons assembled from three squares.** In the
situation of `CategoryTheory.transition_transport_comparison`, let the comparisons `cn`, `cm` be
assembled as in `CategoryTheory.transport_comparison_three` from `σ`, `ε`, `ν`, and let `Lan` be
a left derived functor of `an ⋙ q₅` along the localization `q₀`. If the identity holds upstairs,
then `Lsn T ≫ cn = β ≫ Lx cm ≫ θ` at every object. -/
theorem transition_transport_comparison_of_squares
    {H₀ : Type u₀} {H₁ : Type u₁} {H₂ : Type u₂} {H₃ : Type u₃} {H₄ : Type u₄}
    {H₅ : Type u₅} {H₆ : Type u₆} [Category.{v₀} H₀] [Category.{v₁} H₁] [Category.{v₂} H₂]
    [Category.{v₃} H₃] [Category.{v₄} H₄] [Category.{v₅} H₅] [Category.{v₆} H₆]
    {D₀ : Type t₀} {D₁ : Type t₁} {D₂ : Type t₂} {D₃ : Type t₃} {D₄ : Type t₄}
    {D₅ : Type t₅} {D₆ : Type t₆} [Category.{w₀} D₀] [Category.{w₁} D₁] [Category.{w₂} D₂]
    [Category.{w₃} D₃] [Category.{w₄} D₄] [Category.{w₅} D₅] [Category.{w₆} D₆]
    {q₀ : H₀ ⥤ D₀} {q₁ : H₁ ⥤ D₁} {q₂ : H₂ ⥤ D₂} {q₃ : H₃ ⥤ D₃} {q₄ : H₄ ⥤ D₄}
    {q₅ : H₅ ⥤ D₅} {q₆ : H₆ ⥤ D₆}
    {Lb : D₀ ⥤ D₁} {Rm : D₁ ⥤ D₂} {Rn : D₁ ⥤ D₃} {Lf : D₂ ⥤ D₃} {Lsn : D₃ ⥤ D₅}
    {Lsm : D₂ ⥤ D₄} {Lx : D₄ ⥤ D₅} {Lam : D₀ ⥤ D₄} {Lan : D₀ ⥤ D₅}
    {Le : D₁ ⥤ D₆} {La : D₀ ⥤ D₆} {Ldn : D₆ ⥤ D₅} {Ldm : D₆ ⥤ D₄}
    {b : H₀ ⥤ H₁} {rm : H₁ ⥤ H₂} {rn : H₁ ⥤ H₃} {f : H₂ ⥤ H₃} {sn : H₃ ⥤ H₅}
    {sm : H₂ ⥤ H₄} {x : H₄ ⥤ H₅} {am : H₀ ⥤ H₄} {an : H₀ ⥤ H₅}
    {e : H₁ ⥤ H₆} {a : H₀ ⥤ H₆} {dn : H₆ ⥤ H₅} {dm : H₆ ⥤ H₄}
    (αb : q₀ ⋙ Lb ⟶ b ⋙ q₁) (eRm : q₁ ⋙ Rm ⟶ rm ⋙ q₂) (eRn : q₁ ⋙ Rn ⟶ rn ⋙ q₃)
    (αf : q₂ ⋙ Lf ⟶ f ⋙ q₃) (αsn : q₃ ⋙ Lsn ⟶ sn ⋙ q₅) (αsm : q₂ ⋙ Lsm ⟶ sm ⋙ q₄)
    (αx : q₄ ⋙ Lx ⟶ x ⋙ q₅) (αam : q₀ ⋙ Lam ⟶ am ⋙ q₄) (αan : q₀ ⋙ Lan ⟶ an ⋙ q₅)
    (αe : q₁ ⋙ Le ⟶ e ⋙ q₆) (αa : q₀ ⋙ La ⟶ a ⋙ q₆) (αdn : q₆ ⋙ Ldn ⟶ dn ⋙ q₅)
    (αdm : q₆ ⋙ Ldm ⟶ dm ⋙ q₄)
    (W : MorphismProperty H₀) [q₀.IsLocalization W] [Lan.IsLeftDerivedFunctor αan W]
    (T : Rm ⋙ Lf ⟶ Rn)
    (τ : rm ⋙ f ⟶ rn) (σ₀n : e ⋙ dn ≅ rn ⋙ sn) (σ₀m : e ⋙ dm ≅ rm ⋙ sm) (ε₀ : b ⋙ e ⟶ a)
    (ν₀n : a ⋙ dn ⟶ an) (ν₀m : a ⋙ dm ⟶ am) (β₀ : f ⋙ sn ⟶ sm ⋙ x) (θ₀ : am ⋙ x ⟶ an)
    (cn : Lb ⋙ Rn ⋙ Lsn ⟶ Lan) (cm : Lb ⋙ Rm ⋙ Lsm ⟶ Lam)
    (σn : Le ⋙ Ldn ≅ Rn ⋙ Lsn) (σm : Le ⋙ Ldm ≅ Rm ⋙ Lsm) (ε : Lb ⋙ Le ≅ La)
    (νn : La ⋙ Ldn ≅ Lan) (νm : La ⋙ Ldm ≅ Lam) (β : Lf ⋙ Lsn ⟶ Lsm ⋙ Lx) (θ : Lam ⋙ Lx ⟶ Lan)
    (hT : ∀ X, T.app (q₁.obj X) ≫ eRn.app X =
      Lf.map (eRm.app X) ≫ αf.app (rm.obj X) ≫ q₃.map (τ.app X))
    (hcn : ∀ K, cn.app K = σn.inv.app (Lb.obj K) ≫ 𝟙 _ ≫ Ldn.map (ε.hom.app K) ≫ νn.hom.app K)
    (hcm : ∀ K, cm.app K = σm.inv.app (Lb.obj K) ≫ 𝟙 _ ≫ Ldm.map (ε.hom.app K) ≫ νm.hom.app K)
    (hσn : ∀ N, σn.hom.app (q₁.obj N) ≫ Lsn.map (eRn.app N) ≫ αsn.app (rn.obj N) =
      Ldn.map (αe.app N) ≫ αdn.app (e.obj N) ≫ q₅.map (σ₀n.hom.app N))
    (hσm : ∀ N, σm.hom.app (q₁.obj N) ≫ Lsm.map (eRm.app N) ≫ αsm.app (rm.obj N) =
      Ldm.map (αe.app N) ≫ αdm.app (e.obj N) ≫ q₄.map (σ₀m.hom.app N))
    (hε : ∀ M, ε.hom.app (q₀.obj M) ≫ αa.app M =
      Le.map (αb.app M) ≫ αe.app (b.obj M) ≫ q₆.map (ε₀.app M))
    (hνn : ∀ M, νn.hom.app (q₀.obj M) ≫ αan.app M =
      Ldn.map (αa.app M) ≫ αdn.app (a.obj M) ≫ q₅.map (ν₀n.app M))
    (hνm : ∀ M, νm.hom.app (q₀.obj M) ≫ αam.app M =
      Ldm.map (αa.app M) ≫ αdm.app (a.obj M) ≫ q₄.map (ν₀m.app M))
    (hβ : ∀ N, β.app (q₂.obj N) ≫ Lx.map (αsm.app N) ≫ αx.app (sm.obj N) =
      Lsn.map (αf.app N) ≫ αsn.app (f.obj N) ≫ q₅.map (β₀.app N))
    (hθ : ∀ M, θ.app (q₀.obj M) ≫ αan.app M =
      Lx.map (αam.app M) ≫ αx.app (am.obj M) ≫ q₅.map (θ₀.app M))
    (hS : TransitionHomotopyIdentity τ σ₀n σ₀m ε₀ ν₀n ν₀m β₀ θ₀)
    :
    Functor.whiskerLeft Lb (Functor.whiskerRight T Lsn) ≫ cn =
      Functor.whiskerLeft (Lb ⋙ Rm) β ≫ Functor.whiskerRight cm Lx ≫ θ := by
  have key := transition_transport_comparison αb eRm eRn αf αsn αsm αx αam αan T τ cn
    (fun M ↦ σ₀n.inv.app (b.obj M) ≫ dn.map (ε₀.app M) ≫ ν₀n.app M) cm
    (fun M ↦ σ₀m.inv.app (b.obj M) ≫ dm.map (ε₀.app M) ≫ ν₀m.app M) β β₀ θ θ₀ hT
    (transport_comparison_three αb αe αa αdn eRn αsn αan σn σ₀n ε ε₀ νn ν₀n cn hcn hσn hε hνn)
    (transport_comparison_three αb αe αa αdm eRm αsm αam σm σ₀m ε ε₀ νm ν₀m cm hcm hσm hε hνm)
    hβ hθ hS.eq
  exact Functor.leftDerived_ext Lan αan W (Lb ⋙ Rm ⋙ Lf ⋙ Lsn)
    (Functor.whiskerLeft Lb (Functor.whiskerRight T Lsn) ≫ cn)
    (Functor.whiskerLeft (Lb ⋙ Rm) β ≫ Functor.whiskerRight cm Lx ≫ θ)
    (NatTrans.ext (funext fun M ↦ by
      simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Functor.comp_obj, Category.assoc] using key M))

/-- **The upstairs transition identity from a degreewise one.** Let the transformations
`σn`, `ε`, `νn`, `σm`, `νm`, `β`, `θ` of functors between homotopy categories induced by additive
functors be, at every complex, the transformations induced degreewise by `σn'`, `ε'`, … . If the
identity of `CategoryTheory.transition_transport_comparison_of_squares` holds degreewise, at
every object, for the primed transformations, then it holds on homotopy categories. -/
theorem transition_homotopy_of_degreewise {ι : Type*} {c : ComplexShape ι}
    {A₀ A₁ A₂ A₃ A₄ A₅ A₆ : Type*} {_ : Category* A₀} {_ : Category* A₁} {_ : Category* A₂}
    {_ : Category* A₃} {_ : Category* A₄} {_ : Category* A₅} {_ : Category* A₆}
    {_ : Preadditive A₀} {_ : Preadditive A₁} {_ : Preadditive A₂} {_ : Preadditive A₃}
    {_ : Preadditive A₄} {_ : Preadditive A₅} {_ : Preadditive A₆}
    {B : A₀ ⥤ A₁} {Pm : A₁ ⥤ A₂} {Pn : A₁ ⥤ A₃} {U : A₂ ⥤ A₃} {Sn : A₃ ⥤ A₅}
    {Sm : A₂ ⥤ A₄} {Xf : A₄ ⥤ A₅} {Am : A₀ ⥤ A₄} {An : A₀ ⥤ A₅} {E : A₁ ⥤ A₆}
    {Aa : A₀ ⥤ A₆} {Dn : A₆ ⥤ A₅} {Dm : A₆ ⥤ A₄}
    {_ : B.Additive} {_ : Pm.Additive} {_ : Pn.Additive} {_ : U.Additive} {_ : Sn.Additive}
    {_ : Sm.Additive} {_ : Xf.Additive} {_ : Am.Additive} {_ : An.Additive} {_ : E.Additive}
    {_ : Aa.Additive} {_ : Dn.Additive} {_ : Dm.Additive}
    (t : Pm ⋙ U ⟶ Pn)
    (σn : E.mapHomotopyCategory c ⋙ Dn.mapHomotopyCategory c ≅
      Pn.mapHomotopyCategory c ⋙ Sn.mapHomotopyCategory c)
    (σm : E.mapHomotopyCategory c ⋙ Dm.mapHomotopyCategory c ≅
      Pm.mapHomotopyCategory c ⋙ Sm.mapHomotopyCategory c)
    (ε : B.mapHomotopyCategory c ⋙ E.mapHomotopyCategory c ⟶ Aa.mapHomotopyCategory c)
    (νn : Aa.mapHomotopyCategory c ⋙ Dn.mapHomotopyCategory c ⟶ An.mapHomotopyCategory c)
    (νm : Aa.mapHomotopyCategory c ⋙ Dm.mapHomotopyCategory c ⟶ Am.mapHomotopyCategory c)
    (β : U.mapHomotopyCategory c ⋙ Sn.mapHomotopyCategory c ⟶
      Sm.mapHomotopyCategory c ⋙ Xf.mapHomotopyCategory c)
    (θ : Am.mapHomotopyCategory c ⋙ Xf.mapHomotopyCategory c ⟶ An.mapHomotopyCategory c)
    (σn' : Pn ⋙ Sn ⟶ E ⋙ Dn) (σm' : Pm ⋙ Sm ⟶ E ⋙ Dm) (ε' : B ⋙ E ⟶ Aa)
    (νn' : Aa ⋙ Dn ⟶ An) (νm' : Aa ⋙ Dm ⟶ Am) (β' : U ⋙ Sn ⟶ Sm ⋙ Xf)
    (θ' : Am ⋙ Xf ⟶ An)
    (hσn : ∀ K, σn.inv.app ((HomotopyCategory.quotient A₁ c).obj K) =
      (HomotopyCategory.quotient A₅ c).map ((NatTrans.mapHomologicalComplex σn' c).app K))
    (hσm : ∀ K, σm.inv.app ((HomotopyCategory.quotient A₁ c).obj K) =
      (HomotopyCategory.quotient A₄ c).map ((NatTrans.mapHomologicalComplex σm' c).app K))
    (hε : ∀ K, ε.app ((HomotopyCategory.quotient A₀ c).obj K) =
      (HomotopyCategory.quotient A₆ c).map ((NatTrans.mapHomologicalComplex ε' c).app K))
    (hνn : ∀ K, νn.app ((HomotopyCategory.quotient A₀ c).obj K) =
      (HomotopyCategory.quotient A₅ c).map ((NatTrans.mapHomologicalComplex νn' c).app K))
    (hνm : ∀ K, νm.app ((HomotopyCategory.quotient A₀ c).obj K) =
      (HomotopyCategory.quotient A₄ c).map ((NatTrans.mapHomologicalComplex νm' c).app K))
    (hβ : ∀ K, β.app ((HomotopyCategory.quotient A₂ c).obj K) =
      (HomotopyCategory.quotient A₅ c).map ((NatTrans.mapHomologicalComplex β' c).app K))
    (hθ : ∀ K, θ.app ((HomotopyCategory.quotient A₀ c).obj K) =
      (HomotopyCategory.quotient A₅ c).map ((NatTrans.mapHomologicalComplex θ' c).app K))
    (hsh : ∀ F, Sn.map (t.app (B.obj F)) ≫ σn'.app (B.obj F) ≫ Dn.map (ε'.app F) ≫
        νn'.app F =
      β'.app (Pm.obj (B.obj F)) ≫ Xf.map (σm'.app (B.obj F) ≫ Dm.map (ε'.app F) ≫
        νm'.app F) ≫ θ'.app F) :
    TransitionHomotopyIdentity (mapHomotopyCategoryTransition c Pm U Pn t) σn σm ε νn νm β θ := by
  refine ⟨fun M ↦ ?_⟩
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
  have hc : (Sn.mapHomologicalComplex c).map
        ((NatTrans.mapHomologicalComplex t c).app ((B.mapHomologicalComplex c).obj K)) ≫
      (NatTrans.mapHomologicalComplex σn' c).app ((B.mapHomologicalComplex c).obj K) ≫
      (Dn.mapHomologicalComplex c).map ((NatTrans.mapHomologicalComplex ε' c).app K) ≫
      (NatTrans.mapHomologicalComplex νn' c).app K =
    (NatTrans.mapHomologicalComplex β' c).app
        ((Pm.mapHomologicalComplex c).obj ((B.mapHomologicalComplex c).obj K)) ≫
      (Xf.mapHomologicalComplex c).map
        ((NatTrans.mapHomologicalComplex σm' c).app ((B.mapHomologicalComplex c).obj K) ≫
          (Dm.mapHomologicalComplex c).map ((NatTrans.mapHomologicalComplex ε' c).app K) ≫
          (NatTrans.mapHomologicalComplex νm' c).app K) ≫
      (NatTrans.mapHomologicalComplex θ' c).app K := by
    ext i
    have h := hsh (K.X i)
    simp only [Functor.map_comp, Category.assoc] at h
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      NatTrans.mapHomologicalComplex_app_f, Functor.map_comp, Category.assoc]
    exact h
  have hq := congrArg (HomotopyCategory.quotient A₅ c).map hc
  simp only [Functor.map_comp, ← Functor.mapHomotopyCategory_map, Category.assoc] at hq
  simp only [Functor.map_comp, Category.assoc]
  erw [hσn, hσm, hβ, mapHomotopyCategoryTransition_app, hε, hνn, hνm, hθ]
  exact hq

end CategoryTheory

open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

open AlgebraicGeometry

namespace Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

open Stacks.Cohomology.DerivedPullbackOfToposHom

universe v u w v' u' w' v₁ u₁ w₁ v'' u'' w''

section Degreewise

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Y' : RingedTopos.{v₁, u₁, w₁}} {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Y'.J.HasSheafCompose (forget RingCat.{w₁})] [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Y'.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Y'.J.HasSheafCompose (forget AddCommGrpCat.{w₁})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify Y'.J AddCommGrpCat.{w₁}] [Y'.J.WEqualsLocallyBijective AddCommGrpCat.{w₁}]
  [HasSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]
  (f : RingedToposHom X Y) (g : RingedToposHom Y Z) (f' : RingedToposHom X Y')
  (g' : RingedToposHom Y' Z)

omit [HasSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}] in
/-- The compositor of degreewise pullbacks followed by degreewise pullback of `s`, at a complex. -/
theorem pullbackMapHomotopyCompIso_trans_pullbackModulesIso_hom_app_quotient
    {h : RingedToposHom X Z}
    (s : (g.comp f).toModulesHom.pullbackModules ≅ h.toModulesHom.pullbackModules)
    (K : HomologicalComplex (SheafOfModules.{w''} (SheafOfModules.Tensor.ringSheaf Z.O))
      (ComplexShape.up ℤ)) :
    (pullbackMapHomotopyCompIso f g ≪≫
        Stacks.Homology.mapHomotopyCategoryIso s (ComplexShape.up ℤ)).hom.app
        ((HomotopyCategory.quotient _ _).obj K) =
      (HomotopyCategory.quotient _ _).map ((NatTrans.mapHomologicalComplex
        ((pullbackModulesCompIso f g).inv ≫ s.hom) (ComplexShape.up ℤ)).app K) :=
  rfl

/-- The image in the homotopy category of a composite of natural transformations of functors of
complexes, at a complex. -/
private theorem quotient_map_mapHomologicalComplex_comp_app {ι : Type*} {c : ComplexShape ι}
    {A₁ A₂ : Type*} [Category* A₁] [Category* A₂] [Preadditive A₁] [Preadditive A₂]
    {F G H : A₁ ⥤ A₂} [F.Additive] [G.Additive] [H.Additive] (α : F ⟶ G) (β : G ⟶ H)
    (K : HomologicalComplex A₁ c) :
    (HomotopyCategory.quotient A₂ c).map ((NatTrans.mapHomologicalComplex (α ≫ β) c).app K) =
      (HomotopyCategory.quotient A₂ c).map ((NatTrans.mapHomologicalComplex α c).app K) ≫
        (HomotopyCategory.quotient A₂ c).map ((NatTrans.mapHomologicalComplex β c).app K) := by
  rw [NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app, Functor.map_comp]

omit [HasSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}] in
/-- The degreewise square of Stacks 0D6D at a complex. -/
theorem pullbackMapHomotopySquareIso_hom_app_quotient
    (e : (g.comp f).toModulesHom.pullbackModules ≅ (g'.comp f').toModulesHom.pullbackModules)
    (K : HomologicalComplex (SheafOfModules.{w''} (SheafOfModules.Tensor.ringSheaf Z.O))
      (ComplexShape.up ℤ)) :
    (pullbackMapHomotopySquareIso f g f' g' e).hom.app ((HomotopyCategory.quotient _ _).obj K) =
      (HomotopyCategory.quotient _ _).map ((NatTrans.mapHomologicalComplex
        ((pullbackModulesCompIso f g).inv ≫ e.hom ≫ (pullbackModulesCompIso f' g').hom)
          (ComplexShape.up ℤ)).app K) := by
  simp only [quotient_map_mapHomologicalComplex_comp_app]
  rfl

omit [HasSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}] in
/-- The inverse of the degreewise square of Stacks 0D6D at a complex. -/
theorem pullbackMapHomotopySquareIso_inv_app_quotient
    (e : (g.comp f).toModulesHom.pullbackModules ≅ (g'.comp f').toModulesHom.pullbackModules)
    (K : HomologicalComplex (SheafOfModules.{w''} (SheafOfModules.Tensor.ringSheaf Z.O))
      (ComplexShape.up ℤ)) :
    (pullbackMapHomotopySquareIso f g f' g' e).inv.app ((HomotopyCategory.quotient _ _).obj K) =
      (HomotopyCategory.quotient _ _).map ((NatTrans.mapHomologicalComplex
        ((pullbackModulesCompIso f' g').inv ≫ e.inv ≫ (pullbackModulesCompIso f g).hom)
          (ComplexShape.up ℤ)).app K) := by
  rw [pullbackMapHomotopySquareIso, Iso.trans_inv, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    NatTrans.comp_app]
  simp only [quotient_map_mapHomologicalComplex_comp_app, Category.assoc]
  rfl

omit [HasSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}] in
/-- The degreewise square of Stacks 0D6D followed by an identification `g'^* ≅ P`, inverted, at a
complex. -/
theorem pullbackMapHomotopySquareIso_trans_inv_app_quotient
    (e : (g.comp f).toModulesHom.pullbackModules ≅ (g'.comp f').toModulesHom.pullbackModules)
    {P : SheafOfModules.{w''} (SheafOfModules.Tensor.ringSheaf Z.O) ⥤
      SheafOfModules.{w₁} (SheafOfModules.Tensor.ringSheaf Y'.O)} [P.Additive]
    (r : g'.toModulesHom.pullbackModules ≅ P)
    (K : HomologicalComplex (SheafOfModules.{w''} (SheafOfModules.Tensor.ringSheaf Z.O))
      (ComplexShape.up ℤ)) :
    (pullbackMapHomotopySquareIso f g f' g' e ≪≫
        Functor.isoWhiskerRight (Stacks.Homology.mapHomotopyCategoryIso r.symm
          (ComplexShape.up ℤ)).symm (DerivedPushforward.pullbackMapHomotopy f')).inv.app
        ((HomotopyCategory.quotient _ _).obj K) =
      (HomotopyCategory.quotient _ _).map ((NatTrans.mapHomologicalComplex
        (Functor.whiskerRight r.inv f'.toModulesHom.pullbackModules ≫
          (pullbackModulesCompIso f' g').inv ≫ e.inv ≫ (pullbackModulesCompIso f g).hom)
          (ComplexShape.up ℤ)).app K) := by
  rw [Iso.trans_inv, NatTrans.comp_app, pullbackMapHomotopySquareIso_inv_app_quotient]
  simp only [quotient_map_mapHomologicalComplex_comp_app]
  rfl

end Degreewise

end Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

universe u

-- no global `HasDerivedCategory` instance at this universe
attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : SimplicialObject (AlgebraicSpaces B S hS)} {Z : AlgebraicSpaces B S hS}
  (a : X ⟶ (Functor.const _).obj Z)

/-- **The transition identity on complexes** for the strict system of `b^*M`: the degreewise
transition along `φ`, read through the degreewise component isomorphisms
`realize_n^* g_n^* b^* ≅ a_n^*`, is the degreewise strict square followed by
`X(φ)^* a_m^* ≅ a_n^*`. -/
structure StrictTransitionHomotopyIdentity {m n : SimplexCategory} (φ : m ⟶ n) : Prop where
  /-- The degreewise transition along `φ`, read through the degreewise component isomorphisms, is
  the degreewise strict square followed by `X(φ)^* a_m^* ≅ a_n^*`. -/
  toIdentity : CategoryTheory.TransitionHomotopyIdentity
        (mapHomotopyCategoryTransition (ComplexShape.up ℤ)
          ((strictSituation X).componentModulesRestriction (strictStructureSheaf X) m)
          ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X)
            φ).toModulesHom.pullbackModules
          ((strictSituation X).componentModulesRestriction (strictStructureSheaf X) n)
          ((strictSituation X).componentModulesTransition (strictStructureSheaf X) φ))
        (pullbackMapHomotopySquareIso (degreeRingedToposHom X n)
          (strictRingedToposHom X) (strictComponentRingedToposHom X n)
          ((strictSituation X).componentRingedToposHom (strictStructureSheaf X) n)
          (strictDegreeTwoIso X n).pullbackModulesIso ≪≫
        Functor.isoWhiskerRight (Stacks.Homology.mapHomotopyCategoryIso
          ((strictSituation X).componentPullbackModulesRestrictionIso (strictStructureSheaf X)
            n).symm (ComplexShape.up ℤ)).symm
          (Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
            (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
            (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
            (strictComponentRingedToposHom X n)))
        (pullbackMapHomotopySquareIso (degreeRingedToposHom X m)
          (strictRingedToposHom X) (strictComponentRingedToposHom X m)
          ((strictSituation X).componentRingedToposHom (strictStructureSheaf X) m)
          (strictDegreeTwoIso X m).pullbackModulesIso ≪≫
        Functor.isoWhiskerRight (Stacks.Homology.mapHomotopyCategoryIso
          ((strictSituation X).componentPullbackModulesRestrictionIso (strictStructureSheaf X)
            m).symm (ComplexShape.up ℤ)).symm
          (Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
            (X := spacesEtaleRingedTopos B S hS (X.obj (op m)))
            (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) m)
            (strictComponentRingedToposHom X m)))
        (pullbackMapHomotopyCompIso (strictRingedToposHom X)
          (strictAugmentationRingedToposHom a) ≪≫
          Stacks.Homology.mapHomotopyCategoryIso (strictAugmentationTwoIso a).pullbackModulesIso
            (ComplexShape.up ℤ)).hom
        (pullbackMapHomotopyCompIso (degreeRingedToposHom X n)
          (augmentationRingedToposHom a) ≪≫
          Stacks.Homology.mapHomotopyCategoryIso (augmentationDegreeTwoIso a n).pullbackModulesIso
            (ComplexShape.up ℤ)).hom
        (pullbackMapHomotopyCompIso (degreeRingedToposHom X m)
          (augmentationRingedToposHom a) ≪≫
          Stacks.Homology.mapHomotopyCategoryIso (augmentationDegreeTwoIso a m).pullbackModulesIso
            (ComplexShape.up ℤ)).hom
        (pullbackMapHomotopySquareIso (strictComponentRingedToposHom X n)
          ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) φ)
          (spacesEtaleRingedToposHom (X.map φ.op)) (strictComponentRingedToposHom X m)
          (strictComponentPullbackModulesTransitionIso X φ)).hom
        (pullbackMapHomotopyCompIso (spacesEtaleRingedToposHom (X.map φ.op))
          (spacesEtaleRingedToposHom (a.app (op m))) ≪≫
          Stacks.Homology.mapHomotopyCategoryIso
            (augmentationTransitionTwoIso a φ).pullbackModulesIso
            (ComplexShape.up ℤ)).hom

/-- **The sheaf-level transition identity** for the strict system of `b^*F`: the transition along
`φ`, read through the component isomorphisms `realize_n^* g_n^* b^* ≅ a_n^*` built from the
2-isomorphisms of the strict model, is the strict square followed by `X(φ)^* a_m^* ≅ a_n^*`. -/
structure StrictTransitionSheafIdentity {m n : SimplexCategory} (φ : m ⟶ n) : Prop where
  eq : ∀ F : (spacesEtaleRingedTopos B S hS Z).Modules,
      (strictComponentRingedToposHom X n).toModulesHom.pullbackModules.map
          (((strictSituation X).componentModulesTransition (strictStructureSheaf X) φ).app
            (((strictAugmentationRingedToposHom a).toModulesHom.pullbackModules).obj F)) ≫
        (Functor.whiskerRight
          ((strictSituation X).componentPullbackModulesRestrictionIso (strictStructureSheaf X)
            n).inv
        (strictComponentRingedToposHom X n).toModulesHom.pullbackModules ≫
      (pullbackModulesCompIso (strictComponentRingedToposHom X n)
        ((strictSituation X).componentRingedToposHom (strictStructureSheaf X) n)).inv ≫
      (strictDegreeTwoIso X n).pullbackModulesIso.inv ≫
      (pullbackModulesCompIso (degreeRingedToposHom X n) (strictRingedToposHom X)).hom).app
        (((strictAugmentationRingedToposHom a).toModulesHom.pullbackModules).obj F) ≫
        (degreeRingedToposHom X n).toModulesHom.pullbackModules.map
          (((pullbackModulesCompIso (strictRingedToposHom X)
            (strictAugmentationRingedToposHom a)).inv ≫
      (strictAugmentationTwoIso a).pullbackModulesIso.hom).app F) ≫
        ((pullbackModulesCompIso (degreeRingedToposHom X n) (augmentationRingedToposHom a)).inv ≫
      (augmentationDegreeTwoIso a n).pullbackModulesIso.hom).app F =
      ((pullbackModulesCompIso (strictComponentRingedToposHom X n)
        ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) φ)).inv ≫
      (strictComponentPullbackModulesTransitionIso X φ).hom ≫
      (pullbackModulesCompIso (spacesEtaleRingedToposHom (X.map φ.op))
        (strictComponentRingedToposHom X m)).hom).app
          (((strictSituation X).componentModulesRestriction (strictStructureSheaf X) m).obj
            (((strictAugmentationRingedToposHom a).toModulesHom.pullbackModules).obj F)) ≫
        (spacesEtaleRingedToposHom (X.map φ.op)).toModulesHom.pullbackModules.map
          ((Functor.whiskerRight
            ((strictSituation X).componentPullbackModulesRestrictionIso (strictStructureSheaf X)
              m).inv
        (strictComponentRingedToposHom X m).toModulesHom.pullbackModules ≫
      (pullbackModulesCompIso (strictComponentRingedToposHom X m)
        ((strictSituation X).componentRingedToposHom (strictStructureSheaf X) m)).inv ≫
      (strictDegreeTwoIso X m).pullbackModulesIso.inv ≫
      (pullbackModulesCompIso (degreeRingedToposHom X m) (strictRingedToposHom X)).hom).app
        (((strictAugmentationRingedToposHom a).toModulesHom.pullbackModules).obj F) ≫
          (degreeRingedToposHom X m).toModulesHom.pullbackModules.map
            (((pullbackModulesCompIso (strictRingedToposHom X)
              (strictAugmentationRingedToposHom a)).inv ≫
      (strictAugmentationTwoIso a).pullbackModulesIso.hom).app F) ≫
          ((pullbackModulesCompIso (degreeRingedToposHom X m) (augmentationRingedToposHom a)).inv ≫
      (augmentationDegreeTwoIso a m).pullbackModulesIso.hom).app F) ≫
        ((pullbackModulesCompIso (spacesEtaleRingedToposHom (X.map φ.op))
          (spacesEtaleRingedToposHom (a.app (op m)))).inv ≫
      (augmentationTransitionTwoIso a φ).pullbackModulesIso.hom).app F

/-- Two terms heterogeneously equal to the two sides of an equation are equal. -/
private theorem eq_of_heq_of_eq_of_heq {α β : Sort _} {a a' : α} {b b' : β} (h₁ : HEq a b)
    (h : b = b') (h₂ : HEq b' a') : a = a' :=
  eq_of_heq (h₁.trans ((heq_of_eq h).trans h₂))

/-- The transition identity on complexes follows from the sheaf-level one, degreewise. -/
theorem strictTransitionHomotopyIdentity_of_sheafIdentity {m n : SimplexCategory} (φ : m ⟶ n)
    (hsh : StrictTransitionSheafIdentity a φ) : StrictTransitionHomotopyIdentity a φ := by
  refine ⟨CategoryTheory.transition_homotopy_of_degreewise
      ((strictSituation X).componentModulesTransition (strictStructureSheaf X) φ)
      (pullbackMapHomotopySquareIso (degreeRingedToposHom X n)
        (strictRingedToposHom X) (strictComponentRingedToposHom X n)
        ((strictSituation X).componentRingedToposHom (strictStructureSheaf X) n)
        (strictDegreeTwoIso X n).pullbackModulesIso ≪≫
      Functor.isoWhiskerRight (Stacks.Homology.mapHomotopyCategoryIso
        ((strictSituation X).componentPullbackModulesRestrictionIso (strictStructureSheaf X)
          n).symm (ComplexShape.up ℤ)).symm
        (Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
          (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
          (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
          (strictComponentRingedToposHom X n)))
      (pullbackMapHomotopySquareIso (degreeRingedToposHom X m)
        (strictRingedToposHom X) (strictComponentRingedToposHom X m)
        ((strictSituation X).componentRingedToposHom (strictStructureSheaf X) m)
        (strictDegreeTwoIso X m).pullbackModulesIso ≪≫
      Functor.isoWhiskerRight (Stacks.Homology.mapHomotopyCategoryIso
        ((strictSituation X).componentPullbackModulesRestrictionIso (strictStructureSheaf X)
          m).symm (ComplexShape.up ℤ)).symm
        (Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
          (X := spacesEtaleRingedTopos B S hS (X.obj (op m)))
          (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) m)
          (strictComponentRingedToposHom X m)))
      (pullbackMapHomotopyCompIso (strictRingedToposHom X)
        (strictAugmentationRingedToposHom a) ≪≫
        Stacks.Homology.mapHomotopyCategoryIso (strictAugmentationTwoIso a).pullbackModulesIso
          (ComplexShape.up ℤ)).hom
      (pullbackMapHomotopyCompIso (degreeRingedToposHom X n)
          (augmentationRingedToposHom a) ≪≫
        Stacks.Homology.mapHomotopyCategoryIso (augmentationDegreeTwoIso a n).pullbackModulesIso
          (ComplexShape.up ℤ)).hom
      (pullbackMapHomotopyCompIso (degreeRingedToposHom X m)
          (augmentationRingedToposHom a) ≪≫
        Stacks.Homology.mapHomotopyCategoryIso (augmentationDegreeTwoIso a m).pullbackModulesIso
          (ComplexShape.up ℤ)).hom
      (pullbackMapHomotopySquareIso (strictComponentRingedToposHom X n)
        ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) φ)
        (spacesEtaleRingedToposHom (X.map φ.op)) (strictComponentRingedToposHom X m)
        (strictComponentPullbackModulesTransitionIso X φ)).hom
      (pullbackMapHomotopyCompIso (spacesEtaleRingedToposHom (X.map φ.op))
          (spacesEtaleRingedToposHom (a.app (op m))) ≪≫
        Stacks.Homology.mapHomotopyCategoryIso
          (augmentationTransitionTwoIso a φ).pullbackModulesIso
          (ComplexShape.up ℤ)).hom
      (Functor.whiskerRight
        ((strictSituation X).componentPullbackModulesRestrictionIso (strictStructureSheaf X)
          n).inv
        (strictComponentRingedToposHom X n).toModulesHom.pullbackModules ≫
      (pullbackModulesCompIso (strictComponentRingedToposHom X n)
        ((strictSituation X).componentRingedToposHom (strictStructureSheaf X) n)).inv ≫
      (strictDegreeTwoIso X n).pullbackModulesIso.inv ≫
      (pullbackModulesCompIso (degreeRingedToposHom X n) (strictRingedToposHom X)).hom)
      (Functor.whiskerRight
        ((strictSituation X).componentPullbackModulesRestrictionIso (strictStructureSheaf X)
          m).inv
        (strictComponentRingedToposHom X m).toModulesHom.pullbackModules ≫
      (pullbackModulesCompIso (strictComponentRingedToposHom X m)
        ((strictSituation X).componentRingedToposHom (strictStructureSheaf X) m)).inv ≫
      (strictDegreeTwoIso X m).pullbackModulesIso.inv ≫
      (pullbackModulesCompIso (degreeRingedToposHom X m) (strictRingedToposHom X)).hom)
      ((pullbackModulesCompIso (strictRingedToposHom X) (strictAugmentationRingedToposHom a)).inv ≫
      (strictAugmentationTwoIso a).pullbackModulesIso.hom)
      ((pullbackModulesCompIso (degreeRingedToposHom X n) (augmentationRingedToposHom a)).inv ≫
      (augmentationDegreeTwoIso a n).pullbackModulesIso.hom)
      ((pullbackModulesCompIso (degreeRingedToposHom X m) (augmentationRingedToposHom a)).inv ≫
      (augmentationDegreeTwoIso a m).pullbackModulesIso.hom)
      ((pullbackModulesCompIso (strictComponentRingedToposHom X n)
        ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) φ)).inv ≫
      (strictComponentPullbackModulesTransitionIso X φ).hom ≫
      (pullbackModulesCompIso (spacesEtaleRingedToposHom (X.map φ.op))
        (strictComponentRingedToposHom X m)).hom)
      ((pullbackModulesCompIso (spacesEtaleRingedToposHom (X.map φ.op))
        (spacesEtaleRingedToposHom (a.app (op m)))).inv ≫
      (augmentationTransitionTwoIso a φ).pullbackModulesIso.hom)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · intro K
    exact eq_of_heq_of_eq_of_heq (by heq_congr)
      (pullbackMapHomotopySquareIso_trans_inv_app_quotient
      (degreeRingedToposHom X n) (strictRingedToposHom X) (strictComponentRingedToposHom X n)
      ((strictSituation X).componentRingedToposHom (strictStructureSheaf X) n)
      (strictDegreeTwoIso X n).pullbackModulesIso
      ((strictSituation X).componentPullbackModulesRestrictionIso (strictStructureSheaf X) n) K)
      (by heq_congr)
  · intro K
    exact eq_of_heq_of_eq_of_heq (by heq_congr)
      (pullbackMapHomotopySquareIso_trans_inv_app_quotient
      (degreeRingedToposHom X m) (strictRingedToposHom X) (strictComponentRingedToposHom X m)
      ((strictSituation X).componentRingedToposHom (strictStructureSheaf X) m)
      (strictDegreeTwoIso X m).pullbackModulesIso
      ((strictSituation X).componentPullbackModulesRestrictionIso (strictStructureSheaf X) m) K)
      (by heq_congr)
  · intro K
    exact eq_of_heq_of_eq_of_heq (by heq_congr)
      (pullbackMapHomotopyCompIso_trans_pullbackModulesIso_hom_app_quotient
      (strictRingedToposHom X) (strictAugmentationRingedToposHom a)
      (strictAugmentationTwoIso a).pullbackModulesIso K)
      (by heq_congr)
  · intro K
    exact eq_of_heq_of_eq_of_heq (by heq_congr)
      (pullbackMapHomotopyCompIso_trans_pullbackModulesIso_hom_app_quotient
      (degreeRingedToposHom X n) (augmentationRingedToposHom a)
      (augmentationDegreeTwoIso a n).pullbackModulesIso K)
      (by heq_congr)
  · intro K
    exact eq_of_heq_of_eq_of_heq (by heq_congr)
      (pullbackMapHomotopyCompIso_trans_pullbackModulesIso_hom_app_quotient
      (degreeRingedToposHom X m) (augmentationRingedToposHom a)
      (augmentationDegreeTwoIso a m).pullbackModulesIso K)
      (by heq_congr)
  · intro K
    exact eq_of_heq_of_eq_of_heq (by heq_congr)
      (pullbackMapHomotopySquareIso_hom_app_quotient
        (strictComponentRingedToposHom X n)
        ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) φ)
        (spacesEtaleRingedToposHom (X.map φ.op)) (strictComponentRingedToposHom X m)
        (strictComponentPullbackModulesTransitionIso X φ) K)
      (by heq_congr)
  · intro K
    exact eq_of_heq_of_eq_of_heq (by heq_congr)
      (pullbackMapHomotopyCompIso_trans_pullbackModulesIso_hom_app_quotient
      (spacesEtaleRingedToposHom (X.map φ.op)) (spacesEtaleRingedToposHom (a.app (op m)))
      (augmentationTransitionTwoIso a φ).pullbackModulesIso K)
      (by heq_congr)
  · intro F
    exact eq_of_heq_of_eq_of_heq (by heq_congr) (hsh.eq F) (by heq_congr)

/-- **The transition coherence of the strict system of `Lb^*K`, from its form on complexes.** If
the identity `hhom` holds on homotopy categories of complexes, then the derived transition of the
system `Lb^*K` along `φ`, read through the component isomorphisms
`Lb^* ⋙ D(g_n^{-1}) ⋙ L realize_n^* ≅ La_n^*`, is the derived square of the strict transitions
followed by `La_m^* ⋙ LX(φ)^* ≅ La_n^*`. -/
theorem strictAugmentationDegreeDerivedIso_transition_of_homotopy {m n : SimplexCategory}
    (φ : m ⟶ n)
    (hhom : StrictTransitionHomotopyIdentity a φ) :
    Functor.whiskerLeft (derivedPullback (X := strictRingedTopos X)
        (Y := spacesEtaleRingedTopos B S hS Z) (strictAugmentationRingedToposHom a))
        (Functor.whiskerRight
          ((strictSituation X).derivedComponentModuleTransition (strictStructureSheaf X) φ)
          (derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
            (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
            (strictComponentRingedToposHom X n))) ≫
      (strictAugmentationDegreeDerivedIso a n).hom =
    Functor.whiskerLeft (derivedPullback (X := strictRingedTopos X)
        (Y := spacesEtaleRingedTopos B S hS Z) (strictAugmentationRingedToposHom a))
        (Functor.whiskerLeft
          ((strictSituation X).derivedComponentModuleRestriction (strictStructureSheaf X) m)
          (strictComponentDerivedTransitionIso X φ).hom) ≫
      Functor.whiskerRight (strictAugmentationDegreeDerivedIso a m).hom
        (derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
          (Y := spacesEtaleRingedTopos B S hS (X.obj (op m)))
          (spacesEtaleRingedToposHom (X.map φ.op))) ≫
      (augmentationTransitionDerivedIso a φ).hom := by
  have : (derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
      (Y := spacesEtaleRingedTopos B S hS Z)
      (spacesEtaleRingedToposHom (a.app (op n)))).IsLeftDerivedFunctor
      (derivedPullbackComparison (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := spacesEtaleRingedTopos B S hS Z) (spacesEtaleRingedToposHom (a.app (op n))))
      (quasiIsoTarget (Y := spacesEtaleRingedTopos B S hS Z)) := by
    have := hasLeftDerivedFunctor_pullbackOnHomotopy
      (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
      (Y := spacesEtaleRingedTopos B S hS Z) (spacesEtaleRingedToposHom (a.app (op n)))
    infer_instance
  have KEY := CategoryTheory.transition_transport_comparison_of_squares
    (derivedPullbackComparison (strictAugmentationRingedToposHom a))
    ((strictSituation X).componentModulesRestriction (strictStructureSheaf X)
      m).mapDerivedCategoryFactorsh.hom
    ((strictSituation X).componentModulesRestriction (strictStructureSheaf X)
      n).mapDerivedCategoryFactorsh.hom
    ((strictSituation X).derivedTransitionComparison (strictStructureSheaf X) φ)
    (derivedPullbackComparison (strictComponentRingedToposHom X n))
    (derivedPullbackComparison (strictComponentRingedToposHom X m))
    (derivedPullbackComparison (spacesEtaleRingedToposHom (X.map φ.op)))
    (derivedPullbackComparison (X := spacesEtaleRingedTopos B S hS (X.obj (op m)))
      (Y := spacesEtaleRingedTopos B S hS Z) (spacesEtaleRingedToposHom (a.app (op m))))
    (derivedPullbackComparison (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
      (Y := spacesEtaleRingedTopos B S hS Z) (spacesEtaleRingedToposHom (a.app (op n))))
    (derivedPullbackComparison (strictRingedToposHom X))
    (derivedPullbackComparison (augmentationRingedToposHom a))
    (derivedPullbackComparison (degreeRingedToposHom X n))
    (derivedPullbackComparison (degreeRingedToposHom X m))
    (quasiIsoTarget (Y := spacesEtaleRingedTopos B S hS Z))
    ((strictSituation X).derivedComponentModuleTransition (strictStructureSheaf X) φ)
      (mapHomotopyCategoryTransition (ComplexShape.up ℤ)
        ((strictSituation X).componentModulesRestriction (strictStructureSheaf X) m)
        ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X)
          φ).toModulesHom.pullbackModules
        ((strictSituation X).componentModulesRestriction (strictStructureSheaf X) n)
        ((strictSituation X).componentModulesTransition (strictStructureSheaf X) φ))
      (pullbackMapHomotopySquareIso (degreeRingedToposHom X n)
        (strictRingedToposHom X) (strictComponentRingedToposHom X n)
        ((strictSituation X).componentRingedToposHom (strictStructureSheaf X) n)
        (strictDegreeTwoIso X n).pullbackModulesIso ≪≫
      Functor.isoWhiskerRight (Stacks.Homology.mapHomotopyCategoryIso
        ((strictSituation X).componentPullbackModulesRestrictionIso (strictStructureSheaf X)
          n).symm (ComplexShape.up ℤ)).symm
        (Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
          (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
          (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
          (strictComponentRingedToposHom X n)))
      (pullbackMapHomotopySquareIso (degreeRingedToposHom X m)
        (strictRingedToposHom X) (strictComponentRingedToposHom X m)
        ((strictSituation X).componentRingedToposHom (strictStructureSheaf X) m)
        (strictDegreeTwoIso X m).pullbackModulesIso ≪≫
      Functor.isoWhiskerRight (Stacks.Homology.mapHomotopyCategoryIso
        ((strictSituation X).componentPullbackModulesRestrictionIso (strictStructureSheaf X)
          m).symm (ComplexShape.up ℤ)).symm
        (Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
          (X := spacesEtaleRingedTopos B S hS (X.obj (op m)))
          (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) m)
          (strictComponentRingedToposHom X m)))
      (pullbackMapHomotopyCompIso (strictRingedToposHom X)
        (strictAugmentationRingedToposHom a) ≪≫
        Stacks.Homology.mapHomotopyCategoryIso (strictAugmentationTwoIso a).pullbackModulesIso
          (ComplexShape.up ℤ)).hom
      (pullbackMapHomotopyCompIso (degreeRingedToposHom X n)
        (augmentationRingedToposHom a) ≪≫
        Stacks.Homology.mapHomotopyCategoryIso (augmentationDegreeTwoIso a n).pullbackModulesIso
          (ComplexShape.up ℤ)).hom
      (pullbackMapHomotopyCompIso (degreeRingedToposHom X m)
        (augmentationRingedToposHom a) ≪≫
        Stacks.Homology.mapHomotopyCategoryIso (augmentationDegreeTwoIso a m).pullbackModulesIso
          (ComplexShape.up ℤ)).hom
      (pullbackMapHomotopySquareIso (strictComponentRingedToposHom X n)
        ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) φ)
        (spacesEtaleRingedToposHom (X.map φ.op)) (strictComponentRingedToposHom X m)
        (strictComponentPullbackModulesTransitionIso X φ)).hom
      (pullbackMapHomotopyCompIso (spacesEtaleRingedToposHom (X.map φ.op))
        (spacesEtaleRingedToposHom (a.app (op m))) ≪≫
        Stacks.Homology.mapHomotopyCategoryIso
          (augmentationTransitionTwoIso a φ).pullbackModulesIso
          (ComplexShape.up ℤ)).hom
    (strictAugmentationDegreeDerivedIso a n).hom (strictAugmentationDegreeDerivedIso a m).hom
    (strictDegreeDerivedIso X n) (strictDegreeDerivedIso X m)
    (derivedPullbackCompIso (strictRingedToposHom X) (strictAugmentationRingedToposHom a) ≪≫
        derivedPullbackIsoOfPullbackModulesIso
          (φ := RingedToposHom.comp (X := ringedTopos X) (Y := strictRingedTopos X)
            (Z := spacesEtaleRingedTopos B S hS Z) (strictAugmentationRingedToposHom a)
            (strictRingedToposHom X))
          (ψ := augmentationRingedToposHom a)
          (strictAugmentationTwoIso a).pullbackModulesIso)
    (derivedPullbackCompIso (degreeRingedToposHom X n) (augmentationRingedToposHom a) ≪≫
      derivedPullbackIsoOfPullbackModulesIso
        (φ := RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
          (Y := ringedTopos X) (Z := spacesEtaleRingedTopos B S hS Z)
          (augmentationRingedToposHom a) (degreeRingedToposHom X n))
        (ψ := spacesEtaleRingedToposHom (a.app (op n)))
        (augmentationDegreeTwoIso a n).pullbackModulesIso)
    (derivedPullbackCompIso (degreeRingedToposHom X m) (augmentationRingedToposHom a) ≪≫
      derivedPullbackIsoOfPullbackModulesIso
        (φ := RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op m)))
          (Y := ringedTopos X) (Z := spacesEtaleRingedTopos B S hS Z)
          (augmentationRingedToposHom a) (degreeRingedToposHom X m))
        (ψ := spacesEtaleRingedToposHom (a.app (op m)))
        (augmentationDegreeTwoIso a m).pullbackModulesIso)
    (strictComponentDerivedTransitionIso X φ).hom
    (augmentationTransitionDerivedIso a φ).hom
    ((strictSituation X).derivedComponentModuleTransition_app_Qh (strictStructureSheaf X) φ)
    (fun _ ↦ rfl) (fun _ ↦ rfl)
    (fun N ↦ eq_of_heq_of_eq_of_heq (by heq_congr) (strictDegreeDerivedIso_hom_app_Qh' X n N)
      (by heq_congr))
    (fun N ↦ eq_of_heq_of_eq_of_heq (by heq_congr) (strictDegreeDerivedIso_hom_app_Qh' X m N)
      (by heq_congr))
    (fun M ↦ (Category.assoc _ _ _).trans
      (derivedPullbackCompComparison_app_comp_isoOfPullbackModulesIso_comparison_app
        (strictRingedToposHom X) (strictAugmentationRingedToposHom a)
        (h := augmentationRingedToposHom a) (strictAugmentationTwoIso a).pullbackModulesIso M))
    (augmentationDegreeDerivedIso_hom_app_Qh a n) (augmentationDegreeDerivedIso_hom_app_Qh a m)
    (strictComponentDerivedTransitionIso_hom_app_Qh X φ)
    (augmentationTransitionDerivedIso_hom_app_Qh a φ) hhom.toIdentity
  exact KEY

/-- `strictAugmentationDegreeDerivedIso_transition_of_homotopy` at an object `K` of `D(Z)`. -/
theorem strictAugmentationDegreeDerivedIso_transition_app_of_homotopy {m n : SimplexCategory}
    (φ : m ⟶ n) (hhom : StrictTransitionHomotopyIdentity a φ)
    (K : DerivedCategory (spacesEtaleRingedTopos B S hS Z).Modules) :
    (derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
        (strictComponentRingedToposHom X n)).map
        (((strictSituation X).derivedComponentModuleTransition (strictStructureSheaf X) φ).app
          ((derivedPullback (X := strictRingedTopos X) (Y := spacesEtaleRingedTopos B S hS Z)
          (strictAugmentationRingedToposHom a)).obj K)) ≫
      (strictAugmentationDegreeDerivedIso a n).hom.app K =
    (strictComponentDerivedTransitionIso X φ).hom.app
        (((strictSituation X).derivedComponentModuleRestriction (strictStructureSheaf X) m).obj
          ((derivedPullback (X := strictRingedTopos X) (Y := spacesEtaleRingedTopos B S hS Z)
          (strictAugmentationRingedToposHom a)).obj K)) ≫
      (derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
          (Y := spacesEtaleRingedTopos B S hS (X.obj (op m)))
          (spacesEtaleRingedToposHom (X.map φ.op))).map
        ((strictAugmentationDegreeDerivedIso a m).hom.app K) ≫
      (augmentationTransitionDerivedIso a φ).hom.app K := by
  have h :=
    NatTrans.congr_app (strictAugmentationDegreeDerivedIso_transition_of_homotopy a φ hhom) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h
  exact h


end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite
