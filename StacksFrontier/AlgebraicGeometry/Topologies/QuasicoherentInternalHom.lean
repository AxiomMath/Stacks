module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplex
public import StacksFrontier.CategoryTheory.Sites.Modules.GrothendieckAbelian
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-coherence of the internal Hom out of a finite locally free module

Let `(C, O)` be a ringed site and let `F` and `G` be sheaves of `O`-modules.  The internal Hom
of Stacks 03EM is the sheaf of modules `𝓗om_O(F, G)` whose sections over an object are the
morphisms between the restrictions of `F` and `G` to the slice over it.  It is quasi-coherent as
soon as `F` and `G` are quasi-coherent and `F` is finite locally free.  The statement is made on
an arbitrary ringed site, so it applies to the big Zariski, étale, smooth, syntomic and fppf
sites of a scheme.

## Main results

* `AlgebraicGeometry.RingedSite.internalHomSheaf_isQuasicoherent`: the internal Hom of a finite
  locally free quasi-coherent module into a quasi-coherent module is quasi-coherent.

## Implementation notes

Finite local freeness is the local-generators condition of Stacks 01C6(2) and quasi-coherence is
the condition of Stacks 03DL(6), stated by universal properties, so that no sheafification on the
site itself is needed.  Sheafification on the *slices* is taken as a hypothesis, since the
instance arguments of `SheafOfModules.IsFiniteLocallyFree` require it.

## References

* [Stacks Project, Tag 0GNC](https://stacks.math.columbia.edu/tag/0GNC)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{w}}

/-- Lifting the sections of a sheaf of modules into the universe they already live in does not
change it. -/
public noncomputable def uliftSelfIso (M : _root_.SheafOfModules.{max u v w} R) :
    _root_.SheafOfModules.uliftForPresentation.{u, v, w, max u v w, max u v w} M ≅ M :=
  (_root_.SheafOfModules.fullyFaithfulForget R).preimageIso <| PresheafOfModules.isoMk
    (fun U => by
      letI := (M.val.obj U).isModule
      exact (ULift.moduleEquiv : ULift (M.val.obj U) ≃ₗ[R.obj.obj U] _).toModuleIso)
    (by intros; ext; rfl)

/-- A coproduct of copies of a cokernel is the cokernel of the coproduct of copies of the
presenting map. -/
private noncomputable def coproductCokernel
    {D : Type*} [Category D] [HasZeroMorphisms D]
    {A B M : D} {a : A ⟶ B} {b : B ⟶ M} {hab : a ≫ b = 0}
    (h : IsColimit (CokernelCofork.ofπ b hab))
    (I : Type*) [HasCoproduct (fun _ : I => A)]
    [HasCoproduct (fun _ : I => B)] [HasCoproduct (fun _ : I => M)] :
    IsColimit (CokernelCofork.ofπ (Limits.Sigma.map (fun _ : I => b))
      (show Limits.Sigma.map (fun _ : I => a) ≫ Limits.Sigma.map (fun _ : I => b) = 0 by
        ext i
        simp only [Sigma.ι_map_assoc, Sigma.ι_map, comp_zero]
        rw [← Category.assoc, hab, zero_comp])) := by
  refine CokernelCofork.IsColimit.ofπ _ _ (fun s hs =>
    Sigma.desc (fun i => (CokernelCofork.IsColimit.desc' h (Sigma.ι (fun _ : I => B) i ≫ s)
      (by simpa using congrArg (fun f => Sigma.ι (fun _ : I => A) i ≫ f) hs)).1)) ?_ ?_
  · intro Z s hs
    ext i
    simpa using (CokernelCofork.IsColimit.desc' h (Sigma.ι (fun _ : I => B) i ≫ s) _).2
  · intro Z s hs m hm
    ext i
    apply Cofork.IsColimit.hom_ext h
    simp only [Sigma.ι_desc, CokernelCofork.π_ofπ]
    change b ≫ _ = b ≫ (CokernelCofork.IsColimit.desc' h _ _).1
    exact (show b ≫ Sigma.ι (fun _ : I => M) i ≫ m =
        Sigma.ι (fun _ : I => B) i ≫ s by
      simpa using congrArg (fun f => Sigma.ι (fun _ : I => B) i ≫ f) hm).trans
        (CokernelCofork.IsColimit.desc' h _ _).2.symm

/-- A module isomorphic to a coproduct of copies of a module with a global presentation has a
global presentation. -/
private theorem hasGlobalPresentation_of_coproductIso
    (M : _root_.SheafOfModules.{w} R)
    (N : _root_.SheafOfModules.{max u v w} R) (I : Type w)
    [HasCoproduct (fun _ : I =>
      _root_.SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} M)]
    (e : (∐ fun _ : I =>
      _root_.SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} M) ≅ N)
    (hM : M.HasGlobalPresentation) : N.HasGlobalPresentation := by
  classical
  obtain ⟨K, L, P, Q, ι, κ, hP, hQ, a, b, hab, hc⟩ := hM
  let e' := e ≪≫ (uliftSelfIso N).symm
  let ι' : I × K → _ := fun i => ι i.2 ≫ Sigma.ι (fun _ : I => P) i.1
  let κ' : I × L → _ := fun i => κ i.2 ≫ Sigma.ι (fun _ : I => Q) i.1
  have hP' : IsColimit (Cofan.mk (∐ fun _ : I => P) ι') :=
    Cofan.IsColimit.prod (fun _ : I => Cofan.mk P ι) (fun _ => hP.some)
      _ (coproductIsCoproduct _)
  have hQ' : IsColimit (Cofan.mk (∐ fun _ : I => Q) κ') :=
    Cofan.IsColimit.prod (fun _ : I => Cofan.mk Q κ) (fun _ => hQ.some)
      _ (coproductIsCoproduct _)
  let a' := Limits.Sigma.map (fun _ : I => a)
  let b' := Limits.Sigma.map (fun _ : I => b) ≫ e'.hom
  have hab' : a' ≫ b' = 0 := by
    ext i
    simp only [a', b', Sigma.ι_map_assoc, comp_zero]
    rw [← Category.assoc a b, hab, zero_comp]
  refine ⟨I × K, I × L, _, _, ι', κ', ⟨hP'⟩, ⟨hQ'⟩, a', b', hab', ⟨?_⟩⟩
  exact Cofork.isColimitOfIsos _ (coproductCokernel hc.some I)
    (CokernelCofork.ofπ b' hab') (Iso.refl _) (Iso.refl _) e'

/-- A section of a sheaf of modules over the slice site over an object is the same thing as a
section over that object. -/
private noncomputable def overSectionsEquiv (M : _root_.SheafOfModules.{w} R) (U : C) :
    (M.over U).sections ≃ M.val.obj (op U) where
  toFun s := s.val (op (Over.mk (𝟙 U)))
  invFun x := ⟨fun V => M.val.map V.unop.hom.op x, by
    intro V W f
    change M.val.map f.unop.left.op (M.val.map V.unop.hom.op x) = _
    rw [← M.val.map_comp_apply]
    change M.val.map (f.unop.left ≫ V.unop.hom).op x = _
    rw [f.unop.w]⟩
  left_inv s := by
    apply Subtype.ext
    funext V
    let g : V.unop ⟶ Over.mk (𝟙 U) := Over.homMk V.unop.hom (by simp)
    exact s.property g.op
  right_inv x := by simp

/-- A morphism out of a coproduct is the same thing as a family of morphisms out of its
summands. -/
private noncomputable def cofanHomEquiv
    {D : Type*} [Category D] {I : Type*} {A M N : D}
    (ι : I → (A ⟶ M)) (h : IsColimit (Cofan.mk M ι)) :
    (M ⟶ N) ≃ (I → (A ⟶ N)) where
  toFun f i := ι i ≫ f
  invFun f := Cofan.IsColimit.desc h f
  left_inv f := Cofan.IsColimit.hom_ext h _ _ (fun i => Cofan.IsColimit.fac h _ i)
  right_inv f := by funext i; exact Cofan.IsColimit.fac h f i

end SheafOfModules

/-- A section of the structure sheaf over an object acts on the internal Hom over the terminal
object of the slice at that object as the section itself. -/
private theorem fRestr_terminal {D : Type u} [Category.{v} D]
    (O : Dᵒᵖ ⥤ CommRingCat) (W : D) (r : (ORestr O W).obj (op (Over.mk (𝟙 W)))) :
    fRestr O W r (op (Over.mk (𝟙 W))) = r := by
  simp only [fRestr, Over.mk_hom]
  rw [show (𝟙 W).op = 𝟙 (op W) from rfl, (Oforget O).map_id, RingCat.hom_id]
  rfl

/-- Evaluating a scalar multiple of an internal-Hom section at the terminal object of the slice
is the scalar multiple of the evaluation, the scalar being a section of the restricted ring of
Stacks 03EM. -/
private theorem internalHomObj_smul_eval {D : Type u} [Category.{v} D]
    (O : Dᵒᵖ ⥤ CommRingCat) (M N : PresheafOfModules.{w} (Oforget O)) (W : D)
    (r : (ORestr O W).obj (op (Over.mk (𝟙 W))))
    (α : (restrFun O W).obj M ⟶ (restrFun O W).obj N)
    (y : ((restrFun O W).obj M).obj (op (Over.mk (𝟙 W)))) :
    (smulHom O M N W r α).app (op (Over.mk (𝟙 W))) y
      = r • (α.app (op (Over.mk (𝟙 W))) y) := by
  simp [smulHom, multEndoHom, multEndo, fRestr_terminal]

namespace RingedSite

variable (X : RingedSite.{u, v, w})
  (F G : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- Given a finite basis of `F` on the slice over an object, the sections of the internal Hom
over an object of that slice are the families, indexed by the basis, of sections of `G`. -/
private noncomputable def finiteHomEquiv
    {I : Type w} [Finite I] {U : X.C}
    (ι : I → (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) ⟶
      F.over U))
    (h : IsColimit (Cofan.mk (F.over U) ι)) (V : Over U) :
    ((X.internalHomSheaf F G).val.obj (op V.left)) ≃ (I → G.val.obj (op V.left)) :=
  (_root_.SheafOfModules.fullyFaithfulForget
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V.left)).homEquiv.symm.trans
    ((SheafOfModules.cofanHomEquiv
        (fun i => (_root_.SheafOfModules.overMap
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V.hom).map (ι i))
      (SheafOfModules.overCofanIsColimit F V.hom ι h)).trans
      (Equiv.piCongrRight fun _ => (G.over V.left).unitHomEquiv.trans
        (SheafOfModules.overSectionsEquiv G V.left)))

/-- Evaluation of the internal Hom at a section of `F` over an object, as a morphism from the
internal Hom restricted to the slice over that object to the restriction of `G` there. -/
private noncomputable def basisEval
    {U : X.C}
    (s : _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) ⟶
      F.over U) :
    (X.internalHomSheaf F G).over U ⟶
      _root_.SheafOfModules.uliftForPresentation.{max u v, v, w, w, max u v w} (G.over U) where
  val := {
    app V := by
      letI := (((X.internalHomSheaf F G).over U).val.obj V).isModule
      letI := (G.val.obj (op V.unop.left)).isModule
      exact ModuleCat.homEquiv.symm {
        toFun := fun α => ULift.up (α.app (op (Over.mk (𝟙 V.unop.left)))
          (s.val.app V (1 : X.O.obj.obj (op V.unop.left))))
        map_add' := fun _ _ => rfl
        map_smul' := fun r α => by
          apply ULift.ext
          exact internalHomObj_smul_eval X.O.obj (X.valOf F) (X.valOf G) V.unop.left r α
            (s.val.app V (1 : X.O.obj.obj (op V.unop.left))) }
    naturality := by
      intro V W f
      ext α
      apply ULift.ext
      let g : Over.mk f.unop.left ⟶ Over.mk (𝟙 V.unop.left) :=
        Over.homMk f.unop.left (by simp)
      have h := PresheafOfModules.naturality_apply α g.op
        (s.val.app V (1 : X.O.obj.obj (op V.unop.left)))
      have hs := PresheafOfModules.naturality_apply s.val f (1 : X.O.obj.obj (op V.unop.left))
      change s.val.app W (((Oforget X.O.obj).map f.unop.left.op).hom 1) =
        F.val.map f.unop.left.op (s.val.app V (1 : X.O.obj.obj (op V.unop.left))) at hs
      simp only [map_one] at hs
      change (α.app (op (Over.mk (𝟙 W.unop.left ≫ f.unop.left))))
          (s.val.app W (1 : X.O.obj.obj (op W.unop.left))) =
        G.val.map f.unop.left.op (α.app (op (Over.mk (𝟙 V.unop.left)))
          (s.val.app V (1 : X.O.obj.obj (op V.unop.left))))
      rw [hs]
      have H (k : W.unop.left ⟶ V.unop.left) (hk : k = f.unop.left) :
          (α.app (op (Over.mk k)))
            (F.val.map f.unop.left.op (s.val.app V (1 : X.O.obj.obj (op V.unop.left)))) =
          G.val.map f.unop.left.op
            (α.app (op (Over.mk (𝟙 V.unop.left)))
              (s.val.app V (1 : X.O.obj.obj (op V.unop.left)))) := by
        subst k
        exact h
      exact H _ (Category.id_comp _) }

/-- Given a finite basis of `F` on the slice over an object, the internal Hom restricted to
that slice is the product, indexed by the basis, of copies of the restriction of `G`: the
comparison map is `basisEval` in each coordinate. -/
private noncomputable def basisPiIso
    {I : Type w} [Finite I] {U : X.C}
    (ι : I → (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) ⟶
      F.over U))
    (h : IsColimit (Cofan.mk (F.over U) ι)) :
    (X.internalHomSheaf F G).over U ≅
      ∏ᶜ (fun _ : I =>
        _root_.SheafOfModules.uliftForPresentation.{max u v, v, w, w, max u v w}
          (G.over U)) := by
  let L := _root_.SheafOfModules.uliftForPresentation.{max u v, v, w, w, max u v w} (G.over U)
  let e : (X.internalHomSheaf F G).over U ⟶ ∏ᶜ (fun _ : I => L) :=
    Pi.lift (fun i => basisEval X F G (ι i))
  have he (V : (Over U)ᵒᵖ) : IsIso (e.val.app V) := by
    let ev :=
      _root_.SheafOfModules.evaluation ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) V
    let p := PreservesProduct.iso ev (fun _ : I => L) ≪≫
      ModuleCat.piIsoPi (fun _ : I => ev.obj L)
    let l := ev.map e ≫ p.hom
    have hl : (fun α => l.hom α) =
        fun α i => ULift.up (finiteHomEquiv X F G ι h V.unop α i) := by
      funext α i
      have hi : l ≫ ModuleCat.ofHom (LinearMap.proj i) =
          ev.map (basisEval X F G (ι i)) := by
        dsimp only [l, p, Iso.trans_hom]
        rw [Category.assoc, Category.assoc, ModuleCat.piIsoPi_hom_ker_subtype,
          PreservesProduct.iso_hom, piComparison_comp_π, ← ev.map_comp]
        simp only [e, Pi.lift_comp_π]
      change l.hom α i = _
      rw [show l.hom α i = (ev.map (basisEval X F G (ι i))).hom α from
        congrArg (fun f => f.hom α) hi]
      change ULift.up (α.app (op (Over.mk (𝟙 V.unop.left)))
        ((ι i).val.app V (1 : X.O.obj.obj (op V.unop.left)))) =
          ULift.up (α.app (op (Over.mk (𝟙 V.unop.left)))
            ((ι i).val.app (op (Over.mk (𝟙 V.unop.left ≫ V.unop.hom)))
              (1 : X.O.obj.obj (op V.unop.left))))
      have H (k : V.unop.left ⟶ U) (hk : k = V.unop.hom) :
          (ι i).val.app (op (Over.mk k)) (1 : X.O.obj.obj (op V.unop.left)) =
            (ι i).val.app V (1 : X.O.obj.obj (op V.unop.left)) := by
        subst k
        rfl
      exact congrArg (fun x => ULift.up (α.app (op (Over.mk (𝟙 V.unop.left))) x))
        (H _ (Category.id_comp _)).symm
    have hlb : Function.Bijective l := by
      change Function.Bijective (fun α => l.hom α)
      rw [hl]
      exact ((finiteHomEquiv X F G ι h V.unop).trans
        (Equiv.piCongrRight (fun _ => Equiv.ulift.symm))).bijective
    have : IsIso l := (ConcreteCategory.isIso_iff_bijective l).mpr hlb
    have : IsIso (l ≫ p.inv) := inferInstance
    rwa [show l ≫ p.inv = ev.map e by simp [l]] at this
  exact (_root_.SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun V => @asIso _ _ _ _ (e.val.app V) (he V))
      (by intro V W f; exact e.val.naturality f))

/-- Where `F` has a finite basis and `G` has a global presentation, the internal Hom has a
global presentation. -/
private theorem hasGlobalPresentation_internalHom_over
    {I : Type w} [Finite I] {U : X.C}
    (ι : I → (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) ⟶
      F.over U))
    (h : IsColimit (Cofan.mk (F.over U) ι))
    (hG : (G.over U).HasGlobalPresentation) :
    ((X.internalHomSheaf F G).over U).HasGlobalPresentation := by
  let : HasFiniteBiproducts
      (_root_.SheafOfModules.{max u v w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let L := _root_.SheafOfModules.uliftForPresentation.{max u v, v, w, w, max u v w} (G.over U)
  exact SheafOfModules.hasGlobalPresentation_of_coproductIso (G.over U) _ I
    ((biproductIso (fun _ : I => L)).symm ≪≫ (basisPiIso X F G ι h).symm) hG

/-- On a ringed site whose slices admit sheafification of abelian sheaves, the internal Hom of
Stacks 03EM from a finite locally free quasi-coherent module to a quasi-coherent module is
quasi-coherent. -/
@[stacks 0GNC "internal_hom", ega "I 9.1.1" "special case", sga "3 III 0.6" "special case"]
public theorem internalHomSheaf_isQuasicoherent
    [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
    [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [F.IsQuasicoherentOnSite] [G.IsQuasicoherentOnSite]
    [SheafOfModules.IsFiniteLocallyFree.{w, v, u} F] :
    (X.internalHomSheaf F G).IsQuasicoherentOnSite := by
  classical
  obtain ⟨q, hq, hfin⟩ :=
    (inferInstance : SheafOfModules.IsFiniteLocallyFree F).exists_isFiniteLocallyFreeData
  have freeCover (i : q.I) : ∃ (I : Type w) (_ : Finite I)
      (ι : I → (_root_.SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (q.X i)) ⟶ F.over (q.X i))),
      Nonempty (IsColimit (Cofan.mk (F.over (q.X i)) ι)) := by
    let := hfin.isFiniteType i
    refine ⟨(q.generators i).I, inferInstance,
      fun j => _root_.SheafOfModules.ιFree j ≫ (q.generators i).π, ⟨?_⟩⟩
    exact (_root_.SheafOfModules.isColimitFreeCofan _).ofIsoColimit
      (Cocone.ext (@asIso _ _ _ _ (q.generators i).π (hq.isIso i)) (by intro j; rfl))
  constructor
  intro U
  let K := Σ W : X.C, (W ⟶ U) × (Σ i : q.I, W ⟶ q.X i)
  choose dI dV df hcov hpres using fun W : X.C =>
    _root_.SheafOfModules.IsQuasicoherentOnSite.locally_hasGlobalPresentation (M := G) W
  let T := Σ k : K, dI k.1
  let V : T → X.C := fun t => dV t.1.1 t.2
  let f : ∀ t : T, V t ⟶ U := fun t => df t.1.1 t.2 ≫ t.1.2.1
  refine ⟨T, V, f, ?_, ?_⟩
  · apply X.J.transitive (q.coversTop U)
    intro W a ha
    obtain ⟨i, ⟨b⟩⟩ := (Sieve.mem_ofObjects_iff q.X a).mp ha
    apply X.J.superset_covering _ (hcov W)
    intro Z g hg
    obtain ⟨j, k, hk⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
    show (Sieve.ofArrows V f).arrows (g ≫ a)
    rw [Sieve.mem_ofArrows_iff]
    refine ⟨⟨⟨W, a, i, b⟩, j⟩, k, ?_⟩
    dsimp [f, V]
    rw [hk, Category.assoc]
  · intro t
    obtain ⟨I, hI, ι, ⟨hι⟩⟩ := freeCover t.1.2.2.1
    let := hI
    let g := df t.1.1 t.2 ≫ t.1.2.2.2
    exact hasGlobalPresentation_internalHom_over X F G
      (fun i => (_root_.SheafOfModules.overMap
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).map (ι i))
      (SheafOfModules.overCofanIsColimit F g ι hι) (hpres t.1.1 t.2)

end RingedSite

end AlgebraicGeometry

end
