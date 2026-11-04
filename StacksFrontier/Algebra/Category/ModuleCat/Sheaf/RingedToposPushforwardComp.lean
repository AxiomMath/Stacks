module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardFullyFaithful.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.AdditivityOfDirectAndInverseImage
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposComp

/-!
# Direct images of sheaves of modules compose

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` and `g : (Sh(D), O_D) ⟶ (Sh(E), O_E)` be morphisms of
ringed topoi. This file constructs the canonical isomorphism `(g ∘ f)_* ≅ g_* ∘ f_*` on sheaves
of modules and shows that it is compatible with the direct image of the underlying sheaves of
sets. On underlying sheaves of sets the two direct images agree, and the operations of a sheaf of
modules transported along `f_*` and then `g_*` agree with those transported along `(g ∘ f)_*`.

## Main definitions

* `AlgebraicGeometry.RingedTopos.Modules`: sheaves of modules on a ringed topos.
* `AlgebraicGeometry.RingedToposHom.fSharpRing`: the structure map `f^♯ : O_D ⟶ f_*O_C` read
  as a morphism of the underlying sheaves of rings.
* `AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso`: the canonical isomorphism
  `(g ∘ f)_* ≅ f_* ⋙ g_*` on sheaves of modules.

## Main results

* `Stacks.Sheaves.ToposPushforward.moduleAddObj_comp`,
  `Stacks.Sheaves.ToposPushforward.moduleSMulObj_comp`: transporting the addition and the scalar
  multiplication of a sheaf of modules in two steps agrees with transporting them in one.
* `AlgebraicGeometry.RingedToposHom.comp_fSharpRing_underlying`: on underlying sheaves of rings,
  `(g ∘ f)^♯` is `g^♯` followed by `g_*(f^♯)`.
* `AlgebraicGeometry.RingedToposHom.pushforwardModules_additive`: the direct image of sheaves
  of modules is an additive functor.
* `AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso_underlying`: the composition
  isomorphism is the canonical one, i.e. it becomes the identity after the underlying-sheaf
  comparisons.

## References

* [Stacks Project, Tag 0D6E](https://stacks.math.columbia.edu/tag/0D6E)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback
open Stacks.Sheaves.RingedToposModules

namespace Stacks.Sheaves.ToposPushforward

open CategoryTheory Limits Opposite Stacks.Sheaves.ToposPullback

universe tt ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  (O : Sheaf K RingCat.{ww'}) (G : SheafOfModules.{ww'} O)
  (Ψ : Sheaf J (Type ww) ⥤ Type tt) [PreservesFiniteProducts Ψ]

omit [J.HasSheafCompose (forget RingCat.{ww})] in
/-- Transporting the addition of a sheaf of modules in two steps, first along `Φ` and then
along `Ψ`, gives the same operation as transporting it in one step along `Φ ⋙ Ψ`. -/
lemma moduleAddObj_comp (x y : Ψ.obj (Φ.obj (Sheaf.moduleSheaf O G))) :
    Sheaf.moduleAddObj (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O G) Ψ x y =
      Sheaf.moduleAddObj O G (Φ ⋙ Ψ) x y := by
  have e := congrArg
    (fun m ↦ Ψ.map m (CategoryTheory.Functor.prodObjMk (P := Φ ⋙ Ψ)
      (A := Sheaf.moduleSheaf O G) (B := Sheaf.moduleSheaf O G) x y))
    (moduleAdd_map_aux' J Φ O G)
  have e2 : Ψ.map (Limits.prodComparison Φ (Sheaf.moduleSheaf O G) (Sheaf.moduleSheaf O G) ≫
        Sheaf.moduleAddHom (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O G))
        (CategoryTheory.Functor.prodObjMk (P := Φ ⋙ Ψ) (A := Sheaf.moduleSheaf O G)
          (B := Sheaf.moduleSheaf O G) x y) =
      Ψ.map (Sheaf.moduleAddHom (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O G))
        (Ψ.map (Limits.prodComparison Φ (Sheaf.moduleSheaf O G) (Sheaf.moduleSheaf O G))
          (CategoryTheory.Functor.prodObjMk (P := Φ ⋙ Ψ) (A := Sheaf.moduleSheaf O G)
            (B := Sheaf.moduleSheaf O G) x y)) :=
    Ψ.map_comp_apply _ _ _
  exact (e.trans (e2.trans (congrArg
    (fun z ↦ Ψ.map (Sheaf.moduleAddHom (pullbackRingSheaf J Φ O)
      (pullbackModuleObj J Φ O G)) z)
    (map_prodComparison_prodObjMk J Φ Ψ _ _ x y)))).symm

omit [J.HasSheafCompose (forget RingCat.{ww})] [PreservesFiniteProducts Ψ] in
/-- Transporting the negation of a sheaf of modules in two steps agrees with transporting it
in one. -/
lemma moduleNegObj_comp (x : Ψ.obj (Φ.obj (Sheaf.moduleSheaf O G))) :
    Sheaf.moduleNegObj (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O G) Ψ x =
      Sheaf.moduleNegObj O G (Φ ⋙ Ψ) x :=
  (congrArg (fun m ↦ Ψ.map m x) (moduleNeg_map_aux J Φ O G)).symm

omit [J.HasSheafCompose (forget RingCat.{ww})] in
/-- Transporting the zero of a sheaf of modules in two steps agrees with transporting it in
one. -/
lemma moduleZeroObj_comp :
    Sheaf.moduleZeroObj (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O G) Ψ =
      Sheaf.moduleZeroObj O G (Φ ⋙ Ψ) := by
  have e := congrArg
    (fun m ↦ Ψ.map m (default : (Φ ⋙ Ψ).obj (⊤_ (Sheaf K (Type ww')))))
    (moduleZero_map_aux J Φ O G)
  have e2 : Ψ.map (Limits.terminalComparison Φ ≫
        Sheaf.moduleZeroHom (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O G))
        (default : (Φ ⋙ Ψ).obj (⊤_ (Sheaf K (Type ww')))) =
      Ψ.map (Sheaf.moduleZeroHom (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O G))
        (Ψ.map (Limits.terminalComparison Φ)
          (default : (Φ ⋙ Ψ).obj (⊤_ (Sheaf K (Type ww'))))) :=
    Ψ.map_comp_apply _ _ _
  exact (e.trans (e2.trans (congrArg
    (fun z ↦ Ψ.map (Sheaf.moduleZeroHom (pullbackRingSheaf J Φ O)
      (pullbackModuleObj J Φ O G)) z)
    (Subsingleton.elim _ _)))).symm

/-- Transporting the scalar multiplication of a sheaf of modules in two steps agrees with
transporting it in one. -/
lemma moduleSMulObj_comp (r : Ψ.obj (Φ.obj (Sheaf.ringSheaf O)))
    (x : Ψ.obj (Φ.obj (Sheaf.moduleSheaf O G))) :
    Sheaf.moduleSMulObj (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O G) Ψ r x =
      Sheaf.moduleSMulObj O G (Φ ⋙ Ψ) r x := by
  have e := congrArg
    (fun m ↦ Ψ.map m (CategoryTheory.Functor.prodObjMk (P := Φ ⋙ Ψ)
      (A := Sheaf.ringSheaf O) (B := Sheaf.moduleSheaf O G) r x))
    (moduleSMul_map_aux' J Φ O G)
  have e2 : Ψ.map (Limits.prodComparison Φ (Sheaf.ringSheaf O) (Sheaf.moduleSheaf O G) ≫
        Sheaf.moduleSMulHom (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O G))
        (CategoryTheory.Functor.prodObjMk (P := Φ ⋙ Ψ) (A := Sheaf.ringSheaf O)
          (B := Sheaf.moduleSheaf O G) r x) =
      Ψ.map (Sheaf.moduleSMulHom (pullbackRingSheaf J Φ O) (pullbackModuleObj J Φ O G))
        (Ψ.map (Limits.prodComparison Φ (Sheaf.ringSheaf O) (Sheaf.moduleSheaf O G))
          (CategoryTheory.Functor.prodObjMk (P := Φ ⋙ Ψ) (A := Sheaf.ringSheaf O)
            (B := Sheaf.moduleSheaf O G) r x)) :=
    Ψ.map_comp_apply _ _ _
  exact (e.trans (e2.trans (congrArg
    (fun z ↦ Ψ.map (Sheaf.moduleSMulHom (pullbackRingSheaf J Φ O)
      (pullbackModuleObj J Φ O G)) z)
    (map_prodComparison_prodObjMk J Φ Ψ _ _ r x)))).symm

end Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.RingedTopos

universe v u w

/-- The category of sheaves of modules on a ringed topos, taken over the sheaf of rings
underlying its structure sheaf. -/
abbrev Modules (X : RingedTopos.{v, u, w})
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] :=
  SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)

end AlgebraicGeometry.RingedTopos

namespace AlgebraicGeometry.RingedToposHom

universe w w' w'' v u v' u' v'' u''

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]

/-- The structure map of a morphism of ringed topoi, as a map of the underlying sheaves of
rings; it is `AlgebraicGeometry.RingedToposHom.structureRingMap`. -/
noncomputable abbrev fSharpRing (f : RingedToposHom X Y) :
    (Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O ⟶
      pushforwardRingSheaf f.toToposHom ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) :=
  f.structureRingMap

/-- On underlying sheaves of rings, the structure map of a composite is the structure map of
the second morphism followed by the direct image, under the second morphism, of the structure
map of the first. -/
lemma comp_fSharpRing_underlying (g : RingedToposHom Y Z) (f : RingedToposHom X Y) :
    (sheafCompose Z.J (forget RingCat.{w''})).map (g.comp f).fSharpRing =
      (sheafCompose Z.J (forget RingCat.{w''})).map g.fSharpRing ≫
        g.toToposHom.pushforward.map
          ((sheafCompose Y.J (forget RingCat.{w'})).map f.fSharpRing) :=
  comp_fSharp_forget g f

section Modules

open Stacks.Sheaves.RingedToposModules

variable [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]

omit [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})] in
/-- The direct image of sheaves of modules along a morphism of ringed topoi is additive. -/
theorem pushforwardModules_additive (f : RingedToposHom X Y) :
    (pushforwardModules f).Additive :=
  inferInstanceAs (pushforwardModuleFunctor f.toToposHom
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) ⋙
    SheafOfModules.restrictScalars f.fSharpRing).Additive

attribute [instance] pushforwardModules_additive

/-- The underlying morphism of sheaves of sets of a direct image of a morphism of sheaves of
modules is the direct image of the underlying morphism. -/
lemma moduleSheafFunctor_map_pushforwardModules_map (f : RingedToposHom X Y)
    {M N : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)}
    (φ : M ⟶ N) :
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)).map
        ((pushforwardModules f).map φ) =
      f.toToposHom.pushforward.map
        ((Sheaf.moduleSheafFunctor
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)).map φ) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- The comparison isomorphism `(g ∘ f)_*M ≅ g_*(f_*M)` of sheaves of modules, for a single
module `M`. The underlying sheaves of sets are equal and the comparison is the identity on
them. -/
noncomputable def pushforwardModulesCompIsoApp (g : RingedToposHom Y Z)
    (f : RingedToposHom X Y)
    (M : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) :
    (pushforwardModules (g.comp f)).obj M ≅
      (pushforwardModules g).obj ((pushforwardModules f).obj M) where
  hom := ofSheafHom (𝟙 _)
      (fun V x y ↦ (moduleAddObj_comp Y.J f.toToposHom.pushforward
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) M
        (g.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor Z.J V) x y).symm)
      (fun V r x ↦ by
        have hscal := (congrArg (fun m ↦ (Sheaf.sectionsFunctor Z.J V).map m r)
            (comp_fSharpRing_underlying g f)).trans
          ((Sheaf.sectionsFunctor Z.J V).map_comp_apply _ _ r)
        have hA : (r • x) = Sheaf.moduleSMulObj
              ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) M
              ((f.toToposHom.pushforward ⋙ g.toToposHom.pushforward) ⋙
                Sheaf.sectionsFunctor Z.J V)
              ((Sheaf.sectionsFunctor Z.J V).map
                ((sheafCompose Z.J (forget RingCat.{w''})).map (g.comp f).fSharpRing) r) x := by
          refine Eq.trans ?_ (moduleSMulObj_comp Z.J (g.comp f).toToposHom.pushforward
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) M
            (Sheaf.sectionsFunctor Z.J V) _ x)
          refine Eq.trans ?_ (moduleSMulObj_restrictScalars (g.comp f).fSharpRing _
            (Sheaf.sectionsFunctor Z.J V) r x)
          exact (Sheaf.sectionsFunctor_map_moduleSMulHom
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J)) Z.O) _ V r x).symm
        refine hA.trans ((congrArg (fun z ↦ Sheaf.moduleSMulObj
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) M
          ((f.toToposHom.pushforward ⋙ g.toToposHom.pushforward) ⋙
            Sheaf.sectionsFunctor Z.J V) z x) hscal).trans ?_)
        refine Eq.trans (moduleSMulObj_comp Y.J f.toToposHom.pushforward
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) M
          (g.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor Z.J V) _ x).symm ?_
        refine Eq.trans (moduleSMulObj_restrictScalars f.fSharpRing
          (pullbackModuleObj Y.J f.toToposHom.pushforward
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) M)
          (g.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor Z.J V) _ x).symm ?_
        refine Eq.trans (moduleSMulObj_comp Z.J g.toToposHom.pushforward
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) ((pushforwardModules f).obj M)
          (Sheaf.sectionsFunctor Z.J V) _ x).symm ?_
        refine Eq.trans (moduleSMulObj_restrictScalars g.fSharpRing
          (pullbackModuleObj Z.J g.toToposHom.pushforward
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)
            ((pushforwardModules f).obj M))
          (Sheaf.sectionsFunctor Z.J V) r x).symm ?_
        exact Sheaf.sectionsFunctor_map_moduleSMulHom
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J)) Z.O)
          ((pushforwardModules g).obj ((pushforwardModules f).obj M)) V r x)
  inv := ofSheafHom (𝟙 _)
      (fun V x y ↦ moduleAddObj_comp Y.J f.toToposHom.pushforward
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) M
        (g.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor Z.J V) x y)
      (fun V r x ↦ by
        have hscal := (congrArg (fun m ↦ (Sheaf.sectionsFunctor Z.J V).map m r)
            (comp_fSharpRing_underlying g f)).trans
          ((Sheaf.sectionsFunctor Z.J V).map_comp_apply _ _ r)
        refine Eq.trans (Sheaf.sectionsFunctor_map_moduleSMulHom
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J)) Z.O)
          ((pushforwardModules g).obj ((pushforwardModules f).obj M)) V r x).symm ?_
        refine Eq.trans (moduleSMulObj_restrictScalars g.fSharpRing
          (pullbackModuleObj Z.J g.toToposHom.pushforward
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)
            ((pushforwardModules f).obj M))
          (Sheaf.sectionsFunctor Z.J V) r x) ?_
        refine Eq.trans (moduleSMulObj_comp Z.J g.toToposHom.pushforward
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) ((pushforwardModules f).obj M)
          (Sheaf.sectionsFunctor Z.J V) _ x) ?_
        refine Eq.trans (moduleSMulObj_restrictScalars f.fSharpRing
          (pullbackModuleObj Y.J f.toToposHom.pushforward
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) M)
          (g.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor Z.J V) _ x) ?_
        refine Eq.trans (moduleSMulObj_comp Y.J f.toToposHom.pushforward
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) M
          (g.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor Z.J V) _ x) ?_
        refine Eq.trans (congrArg (fun z ↦ Sheaf.moduleSMulObj
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) M
          ((f.toToposHom.pushforward ⋙ g.toToposHom.pushforward) ⋙
            Sheaf.sectionsFunctor Z.J V) z x) hscal.symm) ?_
        refine Eq.trans (moduleSMulObj_comp Z.J (g.comp f).toToposHom.pushforward
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) M
          (Sheaf.sectionsFunctor Z.J V) _ x).symm ?_
        refine Eq.trans (moduleSMulObj_restrictScalars (g.comp f).fSharpRing
          (pullbackModuleObj Z.J (g.comp f).toToposHom.pushforward
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) M)
          (Sheaf.sectionsFunctor Z.J V) r x).symm ?_
        exact Sheaf.sectionsFunctor_map_moduleSMulHom
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J)) Z.O)
          ((pushforwardModules (g.comp f)).obj M) V r x)
  hom_inv_id := hom_ext_moduleSheafFunctor rfl
  inv_hom_id := hom_ext_moduleSheafFunctor rfl

/-- The canonical isomorphism `(g ∘ f)_* ≅ f_* ⋙ g_*` for direct images of sheaves of
modules along morphisms of ringed topoi. -/
noncomputable def pushforwardModulesCompIso (f : RingedToposHom X Y)
    (g : RingedToposHom Y Z) :
    pushforwardModules (g.comp f) ≅ pushforwardModules f ⋙ pushforwardModules g :=
  NatIso.ofComponents (pushforwardModulesCompIsoApp g f) fun φ ↦
    hom_ext_moduleSheafFunctor (Sheaf.hom_ext_sections fun V s ↦
      (congrArg (fun m ↦ (g.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor Z.J V).map m s)
        (moduleSheafFunctor_map_pushforwardModules_map f φ)).symm)

/-- The composition isomorphism has the canonical underlying map: after the underlying-sheaf
comparisons it is the identity on successive direct images. -/
theorem pushforwardModulesCompIso_underlying (f : RingedToposHom X Y)
    (g : RingedToposHom Y Z)
    (M : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) :
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J)) Z.O)).map
        ((pushforwardModulesCompIso f g).hom.app M) ≫
      (pushforwardModulesUnderlyingIso g).hom.app ((pushforwardModules f).obj M) ≫
        g.toToposHom.pushforward.map
          ((pushforwardModulesUnderlyingIso f).hom.app M) =
      (pushforwardModulesUnderlyingIso (g.comp f)).hom.app M := by
  have h1 : (Sheaf.moduleSheafFunctor
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J)) Z.O)).map
      ((pushforwardModulesCompIso f g).hom.app M) = 𝟙 _ := rfl
  have h2 : (pushforwardModulesUnderlyingIso g).hom.app
      ((pushforwardModules f).obj M) = 𝟙 _ := rfl
  have h3 : (pushforwardModulesUnderlyingIso f).hom.app M = 𝟙 _ := rfl
  have h4 : (pushforwardModulesUnderlyingIso (g.comp f)).hom.app M = 𝟙 _ := rfl
  simp only [h1, h2, h3, h4]
  exact ((Category.id_comp _).trans (Category.id_comp _)).trans
    (CategoryTheory.Functor.map_id _ _)

end Modules

end AlgebraicGeometry.RingedToposHom

end
