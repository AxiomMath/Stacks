module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import StacksFrontier.CategoryTheory.Limits.CoproductCokernel
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSite
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHom
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplex
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-!
# Quasi-coherence of the internal Hom out of a finite locally free module

On a ringed site, the internal Hom from a finite locally free quasi-coherent sheaf of modules
to a quasi-coherent sheaf of modules is quasi-coherent.

The argument is local. Over an object `U` on which `F` is free on a finite basis
`ι : I → (𝒪_U ⟶ F|_U)`, evaluation at the basis identifies `Hom(F, G)|_U` with the product of
`I` copies of `G|_U`; a finite product of sheaves of modules is a finite coproduct, and a
finite coproduct of modules with a global presentation has a global presentation. So it
suffices to cover each object of the site by objects over which `F` is free and `G` has a
global presentation, which the two hypotheses provide after a transitivity step.

## Main results

* `AlgebraicGeometry.RingedSite.internalHomSheaf_isQuasicoherent`: the internal Hom from a
  finite locally free quasi-coherent module to a quasi-coherent module is quasi-coherent.
* `AlgebraicGeometry.RingedSite.internalHomSheaf_isFinitePresentationOnSite`: the finite
  refinement of the same statement — the internal Hom from a finite locally free module to a
  module of finite presentation is of finite presentation. The index type of the basis is
  finite, so the product it identifies the internal Hom with is a *finite* coproduct, and a
  finite coproduct of modules with a finite global presentation has a finite global
  presentation.

## Implementation notes

The statement is made on a ringed site, which covers the big Zariski, étale, smooth, syntomic
and fppf sites of a scheme uniformly. Quasi-coherence is the site-level predicate
`SheafOfModules.IsQuasicoherentOnSite`, which asks for a covering by objects carrying a global
presentation, and finite local freeness is
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`.

The internal Hom sheaf itself is `AlgebraicGeometry.RingedSite.internalHomSheaf`, built from
`internalHom` on the slice sites; it is stated for a module universe independent of the site,
and is used here at the site's own universe.

Restricting a sheaf of modules to a slice site is not a transparent operation for instance
resolution: the sections of `M.over U` over an object `V` of the slice carry their module
structure in the spelling of the pushforward presheaf, while the ambient ring is spelled
through `Sheaf.over`. Each comparison between the two spellings is therefore crossed exactly
once, in a place where elaboration happens at default transparency: `basisEvalApp` states the
evaluation map at the `M.over U` spelling and is used as a term in `basisEval`, and the proof
that evaluation at a finite basis is an isomorphism works throughout with
`SheafOfModules.evaluation` rather than with `Hom.val.app`.

The sections of the module and the ring may live in a smaller universe than the site, so the
internal Hom lands in the larger universe `max u v w`; the comparisons therefore pass through
`SheafOfModules.uliftForPresentation`, and `uliftSelfIso` identifies the lift of a module
already in the larger universe with the module itself.

## References

* [Stacks Project, Tag 0GNC](https://stacks.math.columbia.edu/tag/0GNC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w t

namespace AlgebraicGeometry

namespace RingedSite

section Helpers

private theorem coefficientSheafification
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [UnivLE.{u, t}] [UnivLE.{v, t}] : HasSheafify J AddCommGrpCat.{t} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{t, v, u} J

private theorem coefficientLocallyBijective
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [UnivLE.{u, t}] [UnivLE.{v, t}] : J.WEqualsLocallyBijective AddCommGrpCat.{t} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, t, u, t + 1, t} J

/-- A sheaf of modules already in the larger universe is isomorphic to its own lift. -/
private noncomputable def uliftSelfIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} (M : _root_.SheafOfModules.{max u v w} R) :
    _root_.SheafOfModules.uliftForPresentation.{u, v, w, max u v w, max u v w} M ≅ M := by
  refine (_root_.SheafOfModules.fullyFaithfulForget R).preimageIso ?_
  exact PresheafOfModules.isoMk (fun U => by
      letI := (M.val.obj U).isModule
      exact (ULift.moduleEquiv : ULift (M.val.obj U) ≃ₗ[R.obj.obj U] _).toModuleIso)
    (by intros; ext; rfl)

/-- Taking a coproduct of copies of a global presentation of `M` and transporting along an
isomorphism `e` to `N` gives a presentation of `N` by coproducts of copies of the generators. -/
private theorem exists_coproduct_presentation
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} (M : _root_.SheafOfModules.{w} R)
    (N : _root_.SheafOfModules.{max u v w} R) (I : Type w)
    [HasCoproduct (fun _ : I =>
      _root_.SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} M)]
    (e : (∐ fun _ : I =>
      _root_.SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} M) ≅ N)
    {K L : Type*} {P Q : _root_.SheafOfModules.{max u v w} R}
    (ι : K → (_root_.SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w}
      (_root_.SheafOfModules.unit R) ⟶ P))
    (κ : L → (_root_.SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w}
      (_root_.SheafOfModules.unit R) ⟶ Q))
    (hP : IsColimit (Cofan.mk P ι)) (hQ : IsColimit (Cofan.mk Q κ))
    (a : Q ⟶ P)
    (b : P ⟶ _root_.SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} M)
    (hab : a ≫ b = 0) (hc : IsColimit (CokernelCofork.ofπ b hab)) :
    ∃ (P' Q' : _root_.SheafOfModules.{max u v w} R)
      (ι' : I × K → (_root_.SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w}
        (_root_.SheafOfModules.unit R) ⟶ P'))
      (κ' : I × L → (_root_.SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w}
        (_root_.SheafOfModules.unit R) ⟶ Q')),
      Nonempty (IsColimit (Cofan.mk P' ι')) ∧ Nonempty (IsColimit (Cofan.mk Q' κ')) ∧
        ∃ (a' : Q' ⟶ P')
          (b' : P' ⟶ _root_.SheafOfModules.uliftForPresentation.{u, v, w, max u v w, max u v w} N)
          (hab' : a' ≫ b' = 0), Nonempty (IsColimit (CokernelCofork.ofπ b' hab')) := by
  classical
  let : HasSheafify J AddCommGrpCat.{max u v w} :=
    coefficientSheafification.{u, v, max u v w}
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max u v w} :=
    coefficientLocallyBijective.{u, v, max u v w}
  let e' := e ≪≫ (uliftSelfIso N).symm
  let ι' : I × K → _ := fun i => ι i.2 ≫ Sigma.ι (fun _ : I => P) i.1
  let κ' : I × L → _ := fun i => κ i.2 ≫ Sigma.ι (fun _ : I => Q) i.1
  let a' := Limits.Sigma.map (fun _ : I => a)
  let b' := Limits.Sigma.map (fun _ : I => b) ≫ e'.hom
  have hab' : a' ≫ b' = 0 := by
    apply Sigma.hom_ext
    intro i
    simp only [a', b', Sigma.ι_map_assoc, comp_zero]
    rw [← Category.assoc a b, hab, zero_comp]
  exact ⟨_, _, ι', κ',
    ⟨Cofan.IsColimit.prod (fun _ : I => Cofan.mk P ι) (fun _ => hP) _ (coproductIsCoproduct _)⟩,
    ⟨Cofan.IsColimit.prod (fun _ : I => Cofan.mk Q κ) (fun _ => hQ) _ (coproductIsCoproduct _)⟩,
    a', b', hab', ⟨Cofork.isColimitOfIsos _ (coproductCokernel hc I)
      (CokernelCofork.ofπ b' hab') (Iso.refl _) (Iso.refl _) e'⟩⟩

/-- A module isomorphic to a coproduct of copies of a module with a global presentation has a
global presentation. -/
private theorem hasGlobalPresentation_of_coproductIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} (M : _root_.SheafOfModules.{w} R)
    (N : _root_.SheafOfModules.{max u v w} R) (I : Type w)
    [HasCoproduct (fun _ : I =>
      _root_.SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} M)]
    (e : (∐ fun _ : I =>
      _root_.SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} M) ≅ N)
    (hM : M.HasGlobalPresentation) : N.HasGlobalPresentation := by
  obtain ⟨K, L, P, Q, ι, κ, hP, hQ, a, b, hab, hc⟩ := hM
  obtain ⟨P', Q', ι', κ', hP', hQ', a', b', hab', hc'⟩ :=
    exists_coproduct_presentation M N I e ι κ hP.some hQ.some a b hab hc.some
  exact ⟨I × K, I × L, P', Q', ι', κ', hP', hQ', a', b', hab', hc'⟩

/-- The sections of a sheaf of modules over `U` are the global sections of its restriction to
the slice site over `U`. -/
private noncomputable def overSectionsEquiv
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} (M : _root_.SheafOfModules.{w} R) (U : C) :
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

/-- Evaluation at a finite basis identifies the sections of the internal Hom with the
corresponding product of sections of the target. -/
private noncomputable def finiteHomEquiv
    (X : RingedSite.{u, v, w})
    (F G : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {I : Type w} [Finite I] {U : X.C}
    (ι : I → (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) ⟶
      F.over U))
    (h : IsColimit (Cofan.mk (F.over U) ι)) (V : Over U) :
    ((internalHomSheaf X F G).val.obj (op V.left)) ≃ (I → G.val.obj (op V.left)) :=
  (_root_.SheafOfModules.fullyFaithfulForget
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V.left)).homEquiv.symm.trans
    ((cofanHomEquiv
        (fun i => (_root_.SheafOfModules.overMap
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V.hom).map (ι i))
      (SheafOfModules.overCofanIsColimit F V.hom ι h)).trans
      (Equiv.piCongrRight fun _ => (G.over V.left).unitHomEquiv.trans
        (overSectionsEquiv G V.left)))

/-- Evaluation at a single basis section, on the sections over one object of the slice site.

Stated at the spelling `((internalHomSheaf X F G).over U).val.obj V` of the source module, so
that its module structure is found without unfolding `SheafOfModules.over`; the use site in
`basisEval` crosses the two spellings in a single term-mode application. -/
private noncomputable def basisEvalApp
    (X : RingedSite.{u, v, w})
    (F G : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {U : X.C}
    (s : _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) ⟶
      F.over U)
    (V : (Over U)ᵒᵖ) :
    ((internalHomSheaf X F G).over U).val.obj V ⟶
      (_root_.SheafOfModules.uliftForPresentation.{max u v, v, w, w, max u v w}
        (G.over U)).val.obj V := by
  letI := (G.val.obj (op V.unop.left)).isModule
  exact ModuleCat.homEquiv.symm {
    toFun := fun α => ULift.up (α.app (op (Over.mk (𝟙 V.unop.left)))
      (s.val.app V (1 : X.O.obj.obj (op V.unop.left))))
    map_add' := fun _ _ => rfl
    map_smul' := fun r α => by
      change ULift.up (_root_.fRestr X.O.obj (unop ((Over.forget U).op.obj V)) r
          (op (Over.mk (𝟙 V.unop.left))) •
        (α.app (op (Over.mk (𝟙 V.unop.left)))
          (s.val.app V (1 : X.O.obj.obj (op V.unop.left))))) = _
      simp [_root_.fRestr]
      rfl }

/-- Evaluation of the internal Hom at a single basis section. -/
private noncomputable def basisEval
    (X : RingedSite.{u, v, w})
    (F G : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {U : X.C}
    (s : _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) ⟶
      F.over U) :
    (internalHomSheaf X F G).over U ⟶
      _root_.SheafOfModules.uliftForPresentation.{max u v, v, w, w, max u v w}
        (G.over U) where
  val := {
    app V := basisEvalApp X F G s V
    naturality := by
      intro V W f
      ext α
      apply ULift.ext
      let g : Over.mk f.unop.left ⟶ Over.mk (𝟙 V.unop.left) :=
        Over.homMk f.unop.left (by simp)
      have h := PresheafOfModules.naturality_apply α g.op
        (s.val.app V (1 : X.O.obj.obj (op V.unop.left)))
      have hs := PresheafOfModules.naturality_apply s.val f
        (1 : X.O.obj.obj (op V.unop.left))
      change s.val.app W ((X.O.obj.map f.unop.left.op).hom 1) =
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

/-- Evaluation at a finite basis is an isomorphism from the internal Hom onto the
corresponding product. -/
private noncomputable def basisPiIso
    (X : RingedSite.{u, v, w})
    (F G : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {I : Type w} [Finite I] {U : X.C}
    (ι : I → (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) ⟶
      F.over U))
    (h : IsColimit (Cofan.mk (F.over U) ι)) :
    (internalHomSheaf X F G).over U ≅
      ∏ᶜ (fun _ : I =>
        _root_.SheafOfModules.uliftForPresentation.{max u v, v, w, w, max u v w}
          (G.over U)) := by
  let L := _root_.SheafOfModules.uliftForPresentation.{max u v, v, w, w, max u v w}
    (G.over U)
  let e : (internalHomSheaf X F G).over U ⟶ ∏ᶜ (fun _ : I => L) :=
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
          (basisEval X F G (ι i)).val.app V := by
        dsimp only [l, p, Iso.trans_hom]
        rw [Category.assoc, Category.assoc, ModuleCat.piIsoPi_hom_ker_subtype,
          PreservesProduct.iso_hom, piComparison_comp_π]
        change ev.map e ≫ ev.map (Pi.π (fun _ : I => L) i) = _
        rw [← ev.map_comp]
        simp only [e, Pi.lift_π]
        rfl
      change l.hom α i = _
      rw [show l.hom α i = ((basisEval X F G (ι i)).val.app V).hom α from
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
    have hev : ev.map e = l ≫ p.inv := by simp [l]
    have hiso : IsIso (ev.map e) := by rw [hev]; infer_instance
    exact hiso
  exact (_root_.SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun V => @asIso _ _ _ _ _ (he V))
      (by intro V W f; exact e.val.naturality f))

/-- Over an object on which the source is finite free and the target has a global
presentation, the internal Hom has a global presentation. -/
private theorem hasGlobalPresentation_internalHomSheaf_over
    (X : RingedSite.{u, v, w})
    (F G : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {I : Type w} [Finite I] {U : X.C}
    (ι : I → (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) ⟶
      F.over U))
    (h : IsColimit (Cofan.mk (F.over U) ι))
    (hG : (G.over U).HasGlobalPresentation) :
    ((internalHomSheaf X F G).over U).HasGlobalPresentation := by
  let : HasFiniteBiproducts
      (_root_.SheafOfModules.{max u v w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let L := _root_.SheafOfModules.uliftForPresentation.{max u v, v, w, w, max u v w}
    (G.over U)
  exact hasGlobalPresentation_of_coproductIso (G.over U) _ I
    ((biproductIso (fun _ : I => L)).symm ≪≫ (basisPiIso X F G ι h).symm) hG

/-- If `G` satisfies `PG` locally and `PG` on a member over which `F` is finite free implies `PH`
for the internal Hom, then the internal Hom satisfies `PH` locally.  The covering by objects
over which `F` is free is refined by the coverings on which `G` satisfies `PG`. -/
private theorem internalHomSheaf_locally
    (X : RingedSite.{u, v, w})
    (F G : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
    [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [SheafOfModules.IsFiniteLocallyFree.{w, v, u} F]
    (PG : ∀ U : X.C, _root_.SheafOfModules.{w}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) → Prop)
    (PH : ∀ U : X.C, _root_.SheafOfModules.{max u v w}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) → Prop)
    (hG : ∀ U : X.C, ∃ (I : Type (max u v)) (V : I → X.C) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ X.J U ∧ ∀ i, PG (V i) (G.over (V i)))
    (hstep : ∀ {I : Type w} [Finite I] {U : X.C}
      (ι : I → (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) ⟶
        F.over U)),
      IsColimit (Cofan.mk (F.over U) ι) → PG U (G.over U) → PH U ((internalHomSheaf X F G).over U))
    (U : X.C) :
    ∃ (I : Type (max u v)) (V : I → X.C) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ X.J U ∧ ∀ i, PH (V i) ((internalHomSheaf X F G).over (V i)) := by
  classical
  obtain ⟨q, hq, hfin⟩ :=
    (inferInstance : SheafOfModules.IsFiniteLocallyFree F).exists_isFiniteLocallyFreeData
  have := hq
  have freeCover (i : q.I) : ∃ (I : Type w) (_ : Finite I)
      (ι : I → (_root_.SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (q.X i)) ⟶ F.over (q.X i))),
      Nonempty (IsColimit (Cofan.mk (F.over (q.X i)) ι)) := by
    have := hfin.isFiniteType i
    have hiso : IsIso (q.generators i).π := hq.isIso i
    refine ⟨(q.generators i).I, inferInstance,
      fun j => _root_.SheafOfModules.ιFree j ≫ (q.generators i).π, ⟨?_⟩⟩
    exact (_root_.SheafOfModules.isColimitFreeCofan _).ofIsoColimit
      (Cocone.ext (@asIso _ _ _ _ _ hiso) (by intro j; rfl))
  let K := Σ W : X.C, (W ⟶ U) × (Σ i : q.I, W ⟶ q.X i)
  choose dI dV df hcov hpres using hG
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
    change (Sieve.ofArrows V f).arrows (g ≫ a)
    rw [Sieve.mem_ofArrows_iff]
    refine ⟨⟨⟨W, a, i, b⟩, j⟩, k, ?_⟩
    dsimp [f, V]
    rw [hk, Category.assoc]
  · intro t
    obtain ⟨I, hI, ι, ⟨hι⟩⟩ := freeCover t.1.2.2.1
    let := hI
    let g := df t.1.1 t.2 ≫ t.1.2.2.2
    exact hstep
      (fun i =>
        (_root_.SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).map (ι i))
      (SheafOfModules.overCofanIsColimit F g ι hι) (hpres t.1.1 t.2)

end Helpers

/-- Internal Hom from a finite locally free quasi-coherent sheaf is quasi-coherent. -/
@[stacks 0GNC "internal_hom"]
theorem internalHomSheaf_isQuasicoherent
    (X : RingedSite.{u, v, w})
    (F G : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
    [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [F.IsQuasicoherentOnSite] [G.IsQuasicoherentOnSite]
    [SheafOfModules.IsFiniteLocallyFree.{w, v, u} F] :
    (internalHomSheaf X F G).IsQuasicoherentOnSite :=
  ⟨internalHomSheaf_locally X F G (fun _ M => M.HasGlobalPresentation)
    (fun _ M => M.HasGlobalPresentation)
    (fun U => _root_.SheafOfModules.IsQuasicoherentOnSite.locally_hasGlobalPresentation (M := G) U)
    fun ι h hG => hasGlobalPresentation_internalHomSheaf_over X F G ι h hG⟩

/-! ### The finite refinement: finite presentation of the internal Hom -/

section FinitePresentation

/-- Being a colimiting cofan is stable under an equivalence of the index types.  This is
`CategoryTheory.Limits.Cofan.isColimitEquivOfEquiv` with the two coproduct hypotheses of its
ambient section dropped: the reindexing is the whiskering along the induced equivalence of
discrete categories, and needs no coproduct to exist. -/
private noncomputable def cofanReindexIsColimit {D : Type*} [Category D] {I I' : Type*}
    {g : I → D} (ε : I' ≃ I) (c : Cofan g) (h : IsColimit c) :
    IsColimit (Cofan.mk c.pt fun i : I' => c.inj (ε i)) :=
  (IsColimit.whiskerEquivalenceEquiv (Discrete.equivalence ε)) h

/-- A module isomorphic to a coproduct of *finitely many* copies of a module with a finite
global presentation has a finite global presentation.  This is the finite refinement of
`hasGlobalPresentation_of_coproductIso`: the same coproduct of the presenting diagrams, whose
index types `I × Fin n` and `I × Fin k` are then finite and so reindexed by `Fin`, which is the
shape `SheafOfModules.HasFiniteGlobalPresentation` asks for. -/
private theorem hasFiniteGlobalPresentation_of_finiteCoproductIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} (M : _root_.SheafOfModules.{w} R)
    (N : _root_.SheafOfModules.{max u v w} R) (I : Type w) [Finite I]
    [HasCoproduct (fun _ : I =>
      _root_.SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} M)]
    (e : (∐ fun _ : I =>
      _root_.SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} M) ≅ N)
    (hM : M.HasFiniteGlobalPresentation) : N.HasFiniteGlobalPresentation := by
  obtain ⟨n, k, P, Q, ι, κ, hP, hQ, a, b, hab, hc⟩ := hM
  obtain ⟨P', Q', ι', κ', hP', hQ', a', b', hab', hc'⟩ :=
    exists_coproduct_presentation M N I e ι κ hP.some hQ.some a b hab hc.some
  let _ := Fintype.ofFinite I
  exact ⟨Fintype.card (I × Fin n), Fintype.card (I × Fin k), P', Q',
    fun j => ι' ((Fintype.equivFin (I × Fin n)).symm j),
    fun j => κ' ((Fintype.equivFin (I × Fin k)).symm j),
    ⟨cofanReindexIsColimit _ (Cofan.mk _ ι') hP'.some⟩,
    ⟨cofanReindexIsColimit _ (Cofan.mk _ κ') hQ'.some⟩, a', b', hab', hc'⟩


/-- Over an object on which the source is finite free and the target has a finite global
presentation, the internal Hom has a finite global presentation. -/
private theorem hasFiniteGlobalPresentation_internalHomSheaf_over
    (X : RingedSite.{u, v, w})
    (F G : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {I : Type w} [Finite I] {U : X.C}
    (ι : I → (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) ⟶
      F.over U))
    (h : IsColimit (Cofan.mk (F.over U) ι))
    (hG : (G.over U).HasFiniteGlobalPresentation) :
    ((internalHomSheaf X F G).over U).HasFiniteGlobalPresentation := by
  let : HasFiniteBiproducts
      (_root_.SheafOfModules.{max u v w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let L := _root_.SheafOfModules.uliftForPresentation.{max u v, v, w, w, max u v w}
    (G.over U)
  exact hasFiniteGlobalPresentation_of_finiteCoproductIso (G.over U) _ I
    ((biproductIso (fun _ : I => L)).symm ≪≫ (basisPiIso X F G ι h).symm) hG

/-- **The internal Hom from a finite locally free module into a module of finite presentation is
of finite presentation.**  This is the finite refinement of `internalHomSheaf_isQuasicoherent`,
proved by the same argument: the covering witnessing finite local freeness of `F` is refined by
the coverings on which `G` has a finite global presentation, and on each member of the result
evaluation at the basis identifies the internal Hom with a finite coproduct of copies of `G`. -/
theorem internalHomSheaf_isFinitePresentationOnSite
    (X : RingedSite.{u, v, w})
    (F G : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
    [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [G.IsFinitePresentationOnSite]
    [SheafOfModules.IsFiniteLocallyFree.{w, v, u} F] :
    (internalHomSheaf X F G).IsFinitePresentationOnSite :=
  ⟨internalHomSheaf_locally X F G (fun _ M => M.HasFiniteGlobalPresentation)
    (fun _ M => M.HasFiniteGlobalPresentation)
    (fun U => _root_.SheafOfModules.IsFinitePresentationOnSite.locally_hasFiniteGlobalPresentation
      (F := G) U)
    fun ι h hG => hasFiniteGlobalPresentation_internalHomSheaf_over X F G ι h hG⟩

end FinitePresentation

end RingedSite

end AlgebraicGeometry
