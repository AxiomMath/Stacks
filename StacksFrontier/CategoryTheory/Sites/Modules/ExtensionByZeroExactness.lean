module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroAdjunction
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.Pullback
import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-!
# Extension by zero for modules on a site: exactness and the underlying abelian sheaf

Let `R` be a sheaf of rings on a site `(C, J)` and let `U` be an object of `C`. Restriction
along `Over.forget U` sends a sheaf of `R`-modules to a sheaf of `R_U`-modules on the localized
site `C/U`; its left adjoint `j_{U!}` is extension by zero, constructed in Stacks 03DI. This
file proves the two basic properties of that functor.

The first is that `j_{U!}` is exact. Right exactness is formal, since a left adjoint preserves
all colimits. Left exactness comes from the direct-sum formula of Stacks 03DI: the presheaf
whose sheafification is `j_{U!} G` has as its sections over `V` the direct sum of the `G(φ)`
over all `φ : V ⟶ U`, and that formula is natural in `G`. So a monomorphism `G ⟶ H` induces
over each `V` a coproduct of monomorphisms of modules, which is again a monomorphism because
`ModuleCat` satisfies Grothendieck's axiom AB4. Sheafification and the comparison isomorphism
`SheafOfModules.pullbackIso` transport this to `j_{U!}`, which therefore preserves
monomorphisms; preserving monomorphisms and cokernels makes it preserve homology, hence finite
limits.

The second is that `j_{U!}` is compatible with forgetting the module structure: the square
formed by the two extensions by zero and the two forgetful functors to abelian sheaves
commutes up to natural isomorphism. Extension by zero of abelian sheaves is the sheafification
of the left Kan extension along `(Over.forget U).op`, so the content is that the Kan extension
of the underlying abelian presheaf of `G` has the same direct-sum sections as the presheaf
computing `j_{U!} G`. That is proved here by exhibiting the Kan extension's value at `V` as the
coproduct over the maps `V ⟶ U`, which holds because the comma category indexing the Kan
extension colimit has, for each `φ : V ⟶ U`, a terminal-like object `φ` that the colimit
reduces to.

## Main definitions

* `Stacks.Sites.ExtensionByZero.extensionByZeroSummandsMap`: the map of direct sums induced on
  the sections of the extension-by-zero presheaf by a map of sheaves of modules.
* `Stacks.Sites.ExtensionByZero.extensionByZeroCompToSheafIso`: the natural isomorphism filling
  the extension-by-zero square.

## Main results

* `Stacks.Sites.ExtensionByZero.sheafRestrictionIsRightAdjoint`: restriction of sheaves of
  modules along `Over.forget U` is a right adjoint, which is what makes
  `SheafOfModules.pullback` available as `j_{U!}`.
* `Stacks.Sites.ExtensionByZero.extensionByZero_exact`: `j_{U!}` is exact.
* `Stacks.Sites.ExtensionByZero.isIso_lanSigmaDesc`: the left Kan extension of an abelian
  presheaf along `(Over.forget U).op` has over `V` the coproduct of its values at the objects
  `φ : V ⟶ U`, the comparison being induced by the Kan extension unit.

## Implementation notes

Everything is stated for an arbitrary sheaf of rings `R`, which covers the structure sheaf of a
ringed site as a special case, and no new functor is introduced: `j_{U!}` is Mathlib's
`SheafOfModules.pullback` for `Over.forget U` together with the identity map of the restricted
sheaf of rings, exactly as in Stacks 03DI.

`sheafRestrictionIsRightAdjoint` is needed before `SheafOfModules.pullback` can even be written
down, so it precedes both results and is shared by them; that is why exactness and the abelian
comparison live in one module.

`mono_sigmaMap` and `isIso_lanSigmaDesc` are stated without the ambient ringed-site data, since
neither uses it: the first is AB4 for `ModuleCat`, the second a computation of a left Kan
extension along a slice projection.

## References

* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
* [Stacks Project, Tag 08P4](https://stacks.math.columbia.edu/tag/08P4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sites.ExtensionByZero

universe u

/-- A coproduct of monomorphisms of modules is a monomorphism: Grothendieck's axiom AB4 for
`ModuleCat`, specialized to the map of coproducts induced by a family of maps. -/
lemma mono_sigmaMap {R : Type u} [Ring R] {ι : Type u} {A B : ι → ModuleCat.{u} R}
    (p : ∀ i, A i ⟶ B i) (hp : ∀ i, Mono (p i)) : Mono (Limits.Sigma.map p) := by
  have happ : ∀ X : Discrete ι, Mono ((Discrete.natTrans
      (F := Discrete.functor A) (G := Discrete.functor B)
      fun X : Discrete ι => p X.as).app X) := fun ⟨i⟩ => hp i
  have : Mono (Discrete.natTrans (F := Discrete.functor A) (G := Discrete.functor B)
      fun X : Discrete ι => p X.as) := NatTrans.mono_of_mono_app _
  show Mono ((colim (J := Discrete ι) (C := ModuleCat.{u} R)).map
    (Discrete.natTrans (F := Discrete.functor A) (G := Discrete.functor B)
      fun X : Discrete ι => p X.as))
  infer_instance

/-- **Stacks 0F4K.** The left Kan extension along `(Over.forget U).op` is, over `V`, the
coproduct of the values of `F` at the objects `φ : V ⟶ U` of `C/U`, the comparison map being
the one induced by the Kan extension unit on each summand. Applied to the small étale site of
a scheme and an étale `U ⟶ X`, this is the presheaf extension by zero along `U ⟶ X`: its
sections over `V` are the direct sum of the sections of `F` over the lifts `V ⟶ U`. -/
@[stacks 0F4K]
theorem isIso_lanSigmaDesc
    {C : Type u} [Category.{u} C] (U : C)
    [∀ F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u}, (Over.forget U).op.HasLeftKanExtension F]
    (F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u}) (V : C) :
    IsIso (Sigma.desc
      (f := fun φ : V ⟶ U => F.obj (op (Over.mk φ)))
      (P := (((Over.forget U).op.lan.obj F).obj (op V)))
      (fun φ => (((Over.forget U).op.lanUnit.app F).app (op (Over.mk φ))))) := by
  classical
  let L := (Over.forget U).op
  let J := CostructuredArrow L (op V)
  let G := CostructuredArrow.proj L (op V) ⋙ F
  have key {a b : V ⟶ U} (h : a = b) :
      F.map (op (eqToHom (congrArg Over.mk h))) ≫
        Sigma.ι (fun φ : V ⟶ U => F.obj (op (Over.mk φ))) a =
      Sigma.ι (fun φ : V ⟶ U => F.obj (op (Over.mk φ))) b := by
    subst h
    rw [eqToHom_refl]
    exact (congrArg (· ≫ _) (F.map_id _)).trans (Category.id_comp _)
  let ix (j : J) : V ⟶ U := j.hom.unop ≫ j.left.unop.hom
  let k (j : J) : Over.mk (ix j) ⟶ j.left.unop := Over.homMk j.hom.unop (by rfl)
  let terminal (φ : V ⟶ U) : J :=
    CostructuredArrow.mk (S := L) (T := op V) (Y := op (Over.mk φ)) (𝟙 (op V))
  let eta (j : J) : j ⟶ terminal (ix j) :=
    CostructuredArrow.homMk (k j).op (by simp [L, terminal, k])
  let c : Cocone G := Cocone.mk (∐ fun φ : V ⟶ U => F.obj (op (Over.mk φ))) {
    app := fun j => F.map (Opposite.op (k j)) ≫
      Sigma.ι (fun φ : V ⟶ U => F.obj (op (Over.mk φ))) (ix j)
    naturality := by
      intro j j' f
      show F.map f.left ≫ F.map (op (k j')) ≫
          Sigma.ι (fun φ : V ⟶ U => F.obj (op (Over.mk φ))) (ix j') =
        F.map (op (k j)) ≫
          Sigma.ι (fun φ : V ⟶ U => F.obj (op (Over.mk φ))) (ix j)
      have hrel : j'.hom.unop ≫ f.left.unop.left = j.hom.unop :=
        congrArg (fun g => g.unop) (CostructuredArrow.w f)
      have hix : ix j = ix j' := by
        dsimp [ix]
        calc
          j.hom.unop ≫ j.left.unop.hom =
              (j'.hom.unop ≫ f.left.unop.left) ≫ j.left.unop.hom := by rw [← hrel]
          _ = j'.hom.unop ≫ (f.left.unop.left ≫ j.left.unop.hom) := by
            simp [Category.assoc]
          _ = j'.hom.unop ≫ j'.left.unop.hom := by rw [f.left.unop.w]
      let hobj : Over.mk (ix j) = Over.mk (ix j') := congrArg Over.mk hix
      have hmor : eqToHom hobj ≫ k j' ≫ f.left.unop = k j := by
        apply Over.OverMorphism.ext
        show (eqToHom hobj).left ≫ j'.hom.unop ≫ f.left.unop.left = j.hom.unop
        simpa [Category.assoc] using hrel
      have hpath : f.left ≫ op (k j') ≫ op (eqToHom hobj) = op (k j) := by
        apply Quiver.Hom.unop_inj
        show (eqToHom hobj ≫ k j') ≫ f.left.unop = k j
        rwa [Category.assoc]
      have hinj := key hix
      calc
        F.map f.left ≫ F.map (op (k j')) ≫
            Sigma.ι (fun φ : V ⟶ U => F.obj (op (Over.mk φ))) (ix j') =
              F.map f.left ≫ F.map (op (k j')) ≫ F.map (op (eqToHom hobj)) ≫
                  Sigma.ι (fun φ : V ⟶ U => F.obj (op (Over.mk φ))) (ix j) := by rw [← hinj]
        _ = F.map (f.left ≫ op (k j') ≫ op (eqToHom hobj)) ≫
              Sigma.ι (fun φ : V ⟶ U => F.obj (op (Over.mk φ))) (ix j) := by
            simp only [Functor.map_comp, Category.assoc]
        _ = F.map (op (k j)) ≫
              Sigma.ι (fun φ : V ⟶ U => F.obj (op (Over.mk φ))) (ix j) := by rw [hpath] }
  have hterminal (φ : V ⟶ U) :
      c.ι.app (terminal φ) = Sigma.ι (fun ψ : V ⟶ U => F.obj (op (Over.mk ψ))) φ := by
    have hidx : ix (terminal φ) = φ := by simp [ix, terminal]
    have hk : k (terminal φ) = eqToHom (congrArg Over.mk hidx) := by
      apply Over.OverMorphism.ext
      simp [terminal, k]
    show F.map (op (k (terminal φ))) ≫
        Sigma.ι (fun ψ : V ⟶ U => F.obj (op (Over.mk ψ))) (ix (terminal φ)) = _
    rw [hk]
    exact key hidx
  have hc : IsColimit c := IsColimit.mk
    (fun s => Sigma.desc fun φ => s.ι.app (terminal φ))
    (by
      intro s j
      dsimp [c]
      rw [Category.assoc, Sigma.ι_desc]
      have hmap : G.map (eta j) = F.map (op (k j)) := rfl
      rw [← hmap]
      exact s.w (eta j))
    (by
      intro s m hm
      apply Sigma.hom_ext
      intro φ
      calc
        Sigma.ι (fun ψ : V ⟶ U => F.obj (op (Over.mk ψ))) φ ≫ m =
            s.ι.app (terminal φ) := by simpa only [hterminal] using hm (terminal φ)
        _ = Sigma.ι (fun ψ : V ⟶ U => F.obj (op (Over.mk ψ))) φ ≫
            Sigma.desc (fun ψ => s.ι.app (terminal ψ)) := by rw [Sigma.ι_desc])
  let e₁ : (∐ fun φ : V ⟶ U => F.obj (op (Over.mk φ))) ≅ colimit G :=
    hc.coconePointUniqueUpToIso (colimit.isColimit G)
  let e₂ : (((Over.forget U).op.lan.obj F).obj (op V)) ≅ colimit G :=
    Functor.leftKanExtensionObjIsoColimit L F (op V)
  have he :
      Sigma.desc
        (f := fun φ : V ⟶ U => F.obj (op (Over.mk φ)))
        (P := (((Over.forget U).op.lan.obj F).obj (op V)))
        (fun φ => ((Over.forget U).op.lanUnit.app F).app (op (Over.mk φ))) =
          (e₁ ≪≫ e₂.symm).hom := by
    apply Sigma.hom_ext
    intro φ
    have hunit : ((Over.forget U).op.lanUnit.app F).app (op (Over.mk φ)) ≫ e₂.hom =
        colimit.ι G (terminal φ) :=
      Functor.leftKanExtensionUnit_leftKanExtensionObjIsoColimit_hom
        (L := L) (F := F) (X := op (Over.mk φ))
    have hcolim : Sigma.ι (fun ψ : V ⟶ U => F.obj (op (Over.mk ψ))) φ ≫ e₁.hom =
        colimit.ι G (terminal φ) :=
      (congrArg (fun x => x ≫ e₁.hom) (hterminal φ).symm).trans
        (IsColimit.comp_coconePointUniqueUpToIso_hom hc (colimit.isColimit G) (terminal φ))
    rw [Sigma.ι_desc, Iso.trans_hom, Iso.symm_hom, ← Category.assoc, hcolim]
    exact (Iso.eq_comp_inv e₂).2 hunit
  rw [he]
  infer_instance

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  (R : Sheaf J RingCat.{u}) (U : C)
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Restriction of sheaves of modules along `Over.forget U` has a left adjoint, namely
extension by zero. -/
instance sheafRestrictionIsRightAdjoint :
    (SheafOfModules.pushforward.{u} (F := Over.forget U)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).IsRightAdjoint :=
  have := presheafRestrictionIsRightAdjoint J R U
  (SheafOfModules.PullbackConstruction.adjunction.{u}
    (F := Over.forget U) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).isRightAdjoint

/-- The map of direct sums induced on the sections over `V` of the extension-by-zero presheaf by
a map `f : G ⟶ H` of sheaves of `R_U`-modules: on the summand indexed by `φ : V ⟶ U` it is the
component of `f` at `φ`. -/
noncomputable def extensionByZeroSummandsMap {G H : SheafOfModules.{u} (R.over U)}
    (f : G ⟶ H) (V : C) :
    (∐ extensionByZeroSummands J R U G V) ⟶ (∐ extensionByZeroSummands J R U H V) :=
  Limits.Sigma.map
    (g := extensionByZeroSummands J R U G V)
    (f := extensionByZeroSummands J R U H V)
    (fun φ => (f.val.app (op (Over.mk φ)) :
      extensionByZeroSummands J R U G V φ ⟶ extensionByZeroSummands J R U H V φ))

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `extensionByZeroSummandsMap` is a monomorphism as soon as `f` is: each summand component is
a monomorphism of modules, and `ModuleCat` satisfies AB4. -/
lemma extensionByZeroSummandsMap_mono {G H : SheafOfModules.{u} (R.over U)}
    (f : G ⟶ H) (V : C) [Mono f] :
    Mono (extensionByZeroSummandsMap J R U f V) := by
  have hval : Mono f.val := by
    show Mono ((SheafOfModules.forget (R.over U)).map f)
    infer_instance
  refine mono_sigmaMap _ fun φ => ?_
  exact (ModuleCat.mono_iff_injective _).2
    (PresheafOfModules.injective_of_mono f.val (op (Over.mk φ)))

/-- `extensionByZeroPresheafSectionIso_inv_ι` as an equality of morphisms of modules. -/
private lemma sigma_ι_comp_sectionIso_inv (G : SheafOfModules.{u} (R.over U)) (V : C)
    (φ : V ⟶ U) :
    Sigma.ι (extensionByZeroSummands J R U G V) φ ≫
      (extensionByZeroPresheafSectionIso J R U G V).inv =
    ((PresheafOfModules.pullbackPushforwardAdjunction.{u} (F := Over.forget U)
      (R := R.obj) (S := (R.over U).obj)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).unit.app G.val).app
        (op (Over.mk φ)) :=
  eq_of_heq (extensionByZeroPresheafSectionIso_inv_ι J R U G V φ)

/-- The direct-sum formula of Stacks 03DI is natural in the sheaf of modules: the map induced by
`f : G ⟶ H` on the sections of the extension-by-zero presheaf over `V` is
`extensionByZeroSummandsMap`. -/
lemma extensionByZeroSectionMap_naturality
    {G H : SheafOfModules.{u} (R.over U)} (f : G ⟶ H) (V : C) :
    ((PresheafOfModules.pullback.{u} (F := Over.forget U)
        (R := R.obj) (S := (R.over U).obj)
        (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).map f.val).app (op V) ≫
      (extensionByZeroPresheafSectionIso J R U H V).hom =
      (extensionByZeroPresheafSectionIso J R U G V).hom ≫
      extensionByZeroSummandsMap J R U f V := by
  let eG := extensionByZeroPresheafSectionIso J R U G V
  let eH := extensionByZeroPresheafSectionIso J R U H V
  let P : PresheafOfModules (R.over U).obj ⥤ PresheafOfModules R.obj :=
    PresheafOfModules.pullback.{u} (F := Over.forget U)
      (R := R.obj) (S := (R.over U).obj)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom
  let adj : P ⊣ PresheafOfModules.pushforward.{u} (F := Over.forget U)
      (R := R.obj) (S := (R.over U).obj)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom :=
    PresheafOfModules.pullbackPushforwardAdjunction.{u}
      (F := Over.forget U) (R := R.obj) (S := (R.over U).obj)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom
  apply (Iso.inv_comp_eq eG).1
  apply Sigma.hom_ext
  intro φ
  have hG' := sigma_ι_comp_sectionIso_inv J R U G V φ
  have hnat' :
      ((adj.unit.app G.val).app (op (Over.mk φ))) ≫ (P.map f.val).app (op V) =
        f.val.app (op (Over.mk φ)) ≫ ((adj.unit.app H.val).app (op (Over.mk φ))) :=
    (congrArg (fun g => g.app (op (Over.mk φ))) (adj.unit.naturality f.val)).symm
  have hUnit : ((adj.unit.app H.val).app (op (Over.mk φ))) ≫ eH.hom =
      Sigma.ι (extensionByZeroSummands J R U H V) φ :=
    ((Iso.comp_inv_eq eH).1 (sigma_ι_comp_sectionIso_inv J R U H V φ)).symm
  have hι : (f.val.app (op (Over.mk φ)) :
        extensionByZeroSummands J R U G V φ ⟶ extensionByZeroSummands J R U H V φ) ≫
      Sigma.ι (extensionByZeroSummands J R U H V) φ =
      Sigma.ι (extensionByZeroSummands J R U G V) φ ≫
        extensionByZeroSummandsMap J R U f V :=
    (Limits.Sigma.ι_map (g := extensionByZeroSummands J R U G V)
      (f := extensionByZeroSummands J R U H V)
      (fun ψ => (f.val.app (op (Over.mk ψ)) :
        extensionByZeroSummands J R U G V ψ ⟶ extensionByZeroSummands J R U H V ψ)) φ).symm
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun x => x ≫ ((P.map f.val).app (op V) ≫ eH.hom)) hG').trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun x => x ≫ eH.hom) hnat').trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun x => f.val.app (op (Over.mk φ)) ≫ x) hUnit).trans hι)))))

/-- Extension by zero preserves monomorphisms. -/
lemma extensionByZero_preservesMonomorphisms :
    Functor.PreservesMonomorphisms (SheafOfModules.pullback.{u}
      (F := Over.forget U) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))) := by
  have := presheafRestrictionIsRightAdjoint J R U
  constructor
  intro G H f hf
  have hP : Mono ((PresheafOfModules.pullback.{u} (F := Over.forget U)
      (R := R.obj) (S := (R.over U).obj)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).map f.val) := by
    apply PresheafOfModules.mono_of_injective
    intro X
    let V := unop X
    rw [← ModuleCat.mono_iff_injective]
    have hcomp :
        ((PresheafOfModules.pullback.{u} (F := Over.forget U)
          (R := R.obj) (S := (R.over U).obj)
          (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).map f.val).app (op V) =
        ((extensionByZeroPresheafSectionIso J R U G V).hom ≫
          extensionByZeroSummandsMap J R U f V) ≫
            (extensionByZeroPresheafSectionIso J R U H V).inv :=
      (Iso.eq_comp_inv _).2 (extensionByZeroSectionMap_naturality J R U f V)
    have hσ : Mono (extensionByZeroSummandsMap J R U f V) :=
      have : Mono f := hf
      extensionByZeroSummandsMap_mono J R U f V
    have hmono : Mono (((extensionByZeroPresheafSectionIso J R U G V).hom ≫
        extensionByZeroSummandsMap J R U f V) ≫
          (extensionByZeroPresheafSectionIso J R U H V).inv) := by
      have := hσ
      infer_instance
    rw [hcomp]
    exact hmono
  let e := SheafOfModules.pullbackIso (𝟙 (R.over U))
  have hcomp : Mono ((SheafOfModules.forget (R.over U) ⋙
      PresheafOfModules.pullback.{u} (F := Over.forget U)
        (R := R.obj) (S := (R.over U).obj)
        (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom ⋙
      PresheafOfModules.sheafification (𝟙 R.obj)).map f) := by
    show Mono ((PresheafOfModules.sheafification (𝟙 R.obj)).map
      ((PresheafOfModules.pullback.{u} (F := Over.forget U)
        (R := R.obj) (S := (R.over U).obj)
        (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).map f.val))
    have : Mono ((PresheafOfModules.pullback.{u} (F := Over.forget U)
        (R := R.obj) (S := (R.over U).obj)
        (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).map f.val) := hP
    infer_instance
  have hmap : (SheafOfModules.pullback.{u} (F := Over.forget U)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).map f =
      (e.app G).hom ≫ ((SheafOfModules.forget (R.over U) ⋙
        PresheafOfModules.pullback.{u} (F := Over.forget U)
          (R := R.obj) (S := (R.over U).obj)
          (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom ⋙
        PresheafOfModules.sheafification (𝟙 R.obj)).map f) ≫ (e.app H).inv := by
    apply (cancel_mono (e.app H).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact e.hom.naturality f
  rw [hmap]
  have : Mono ((SheafOfModules.forget (R.over U) ⋙
      PresheafOfModules.pullback.{u} (F := Over.forget U)
        (R := R.obj) (S := (R.over U).obj)
        (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom ⋙
      PresheafOfModules.sheafification (𝟙 R.obj)).map f) := hcomp
  infer_instance

/-- **Stacks 03DJ.** Extension by zero of sheaves of modules along the localization `C/U ⟶ C`
is exact. -/
@[stacks 03DJ]
theorem extensionByZero_exact :
    exactFunctor _ _ (SheafOfModules.pullback.{u}
      (F := Over.forget U) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))) := by
  have := presheafRestrictionIsRightAdjoint J R U
  rw [exactFunctor_iff]
  refine ⟨?_, ?_⟩
  · let F := SheafOfModules.pullback.{u} (F := Over.forget U)
        (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))
    let adj := SheafOfModules.pullbackPushforwardAdjunction
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))
    have : (SheafOfModules.pushforward.{u} (F := Over.forget U)
        (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).Additive := by
      constructor
      intro X Y f g
      ext V x
      rfl
    have : F.Additive := adj.left_adjoint_additive
    have : Functor.PreservesMonomorphisms F := extensionByZero_preservesMonomorphisms J R U
    have : PreservesColimits F := adj.leftAdjoint_preservesColimits
    have : Functor.PreservesHomology F :=
      Functor.preservesHomology_of_preservesMonos_and_cokernels F
    exact Functor.preservesFiniteLimits_of_preservesHomology F
  · let F := SheafOfModules.pullback.{u} (F := Over.forget U)
        (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))
    have : PreservesColimitsOfSize.{0, 0} F :=
      (SheafOfModules.pullbackPushforwardAdjunction
        (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).leftAdjoint_preservesColimits
    exact PreservesColimitsOfSize.preservesFiniteColimits F

/-- Extension by zero preserves finite limits. -/
instance instPreservesFiniteLimitsExtensionByZero :
    PreservesFiniteLimits (SheafOfModules.pullback.{u}
      (F := Over.forget U) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))) :=
  ((exactFunctor_iff _).mp (extensionByZero_exact J R U)).1

variable [∀ F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u},
    (Over.forget U).op.HasLeftKanExtension F]

/-- **Stacks 08P4.** Extension by zero commutes with forgetting the module structure: the
square formed by extension by zero for modules, extension by zero for abelian sheaves and the
two forgetful functors commutes up to natural isomorphism. -/
@[stacks 08P4]
noncomputable def extensionByZeroCompToSheafIso :
    SheafOfModules.pullback.{u}
        (F := Over.forget U) (S := R.over U) (R := R)
        (𝟙 (R.over U)) ⋙ SheafOfModules.toSheaf.{u} R ≅
      SheafOfModules.toSheaf.{u} (R.over U) ⋙
        Functor.sheafPullbackConstruction.sheafPullback
          (Over.forget U) AddCommGrpCat.{u} (J.over U) J := by
  classical
  have := presheafRestrictionIsRightAdjoint J R U
  let φs : (R.over U) ⟶ (R.over U) := 𝟙 (R.over U)
  let φ : (R.over U).obj ⟶ ((Over.forget U).op ⋙ R.obj) := φs.hom
  let P := PresheafOfModules.pullback.{u} (F := Over.forget U)
    (R := R.obj) (S := (R.over U).obj) φ
  let Q := Functor.sheafPullbackConstruction.sheafPullback
    (Over.forget U) AddCommGrpCat.{u} (J.over U) J
  let L := (Over.forget U).op
  let Fmod : SheafOfModules.{u} (R.over U) ⥤ PresheafOfModules.{u} R.obj :=
    SheafOfModules.forget (R.over U) ⋙ P
  let FAb : SheafOfModules.{u} (R.over U) ⥤ (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
    SheafOfModules.forget (R.over U) ⋙ PresheafOfModules.toPresheaf (R.over U).obj
  let Lpre := (Functor.whiskeringLeft (Over U)ᵒᵖ Cᵒᵖ AddCommGrpCat.{u}).obj L
  let Fpres := Fmod ⋙ PresheafOfModules.toPresheaf R.obj
  let unitMod := PresheafOfModules.pullbackPushforwardAdjunction.{u} φ
  let τ := PresheafOfModules.pushforwardCompToPresheaf.{u}
    (F := Over.forget U) (R := R.obj) (S := (R.over U).obj) φ
  let η₀ : FAb ⟶ Fpres ⋙ Lpre := {
    app := fun M =>
      (PresheafOfModules.toPresheaf (R.over U).obj).map (unitMod.unit.app M.val) ≫
        τ.hom.app (P.obj M.val)
    naturality := by
      intro M N f
      change (PresheafOfModules.toPresheaf (R.over U).obj).map f.val ≫
          (PresheafOfModules.toPresheaf (R.over U).obj).map (unitMod.unit.app N.val) ≫
            τ.hom.app (P.obj N.val) =
        (PresheafOfModules.toPresheaf (R.over U).obj).map (unitMod.unit.app M.val) ≫
          τ.hom.app (P.obj M.val) ≫
          Lpre.map ((PresheafOfModules.toPresheaf R.obj).map (P.map f.val))
      calc
        _ = (PresheafOfModules.toPresheaf (R.over U).obj).map
              (f.val ≫ unitMod.unit.app N.val) ≫ τ.hom.app (P.obj N.val) := by
            simp [Functor.map_comp, Category.assoc]
        _ = (PresheafOfModules.toPresheaf (R.over U).obj).map
              (unitMod.unit.app M.val ≫
                (PresheafOfModules.pushforward φ).map (P.map f.val)) ≫
              τ.hom.app (P.obj N.val) := by
            congr 1
            exact congrArg
              (fun g => (PresheafOfModules.toPresheaf (R.over U).obj).map g ≫
                τ.hom.app (P.obj N.val)) (unitMod.unit.naturality f.val)
        _ = (PresheafOfModules.toPresheaf (R.over U).obj).map (unitMod.unit.app M.val) ≫
              (PresheafOfModules.toPresheaf (R.over U).obj).map
                ((PresheafOfModules.pushforward φ).map (P.map f.val)) ≫
              τ.hom.app (P.obj N.val) := by
            simp [Functor.map_comp, Category.assoc]
        _ = (PresheafOfModules.toPresheaf (R.over U).obj).map (unitMod.unit.app M.val) ≫
              τ.hom.app (P.obj M.val) ≫
              Lpre.map ((PresheafOfModules.toPresheaf R.obj).map (P.map f.val)) :=
            congrArg (fun g =>
              (PresheafOfModules.toPresheaf (R.over U).obj).map
                (unitMod.unit.app M.val) ≫ g) (τ.hom.naturality (P.map f.val)) }
  let adjLan := L.lanAdjunction AddCommGrpCat.{u}
  let etaApp (M : SheafOfModules.{u} (R.over U)) :=
    (adjLan.homEquiv (FAb.obj M) (Fpres.obj M)).symm (η₀.app M)
  let η : FAb ⋙ L.lan ⟶ Fpres := {
    app := etaApp
    naturality := by
      intro M N f
      apply (adjLan.homEquiv (FAb.obj M) (Fpres.obj N)).injective
      change (adjLan.homEquiv (FAb.obj M) (Fpres.obj N))
          (L.lan.map (FAb.map f) ≫ etaApp N) = _
      calc
        _ = FAb.map f ≫ η₀.app N := by
          rw [adjLan.homEquiv_naturality_left (FAb.map f) (etaApp N)]
          congr 1
          exact Equiv.apply_symm_apply (adjLan.homEquiv (FAb.obj N) (Fpres.obj N))
            (η₀.app N)
        _ = η₀.app M ≫ Lpre.map (Fpres.map f) := η₀.naturality f
        _ = η₀.app M ≫ L.whiskerLeft (Fpres.map f) := rfl
        _ = (adjLan.homEquiv (FAb.obj M) (Fpres.obj M)) (etaApp M) ≫
              L.whiskerLeft (Fpres.map f) := by
            congr 1
            exact (Equiv.apply_symm_apply
              (adjLan.homEquiv (FAb.obj M) (Fpres.obj M)) (η₀.app M)).symm
        _ = (adjLan.homEquiv (FAb.obj M) (Fpres.obj N)) (etaApp M ≫ Fpres.map f) :=
            (adjLan.homEquiv_naturality_right (etaApp M) (Fpres.map f)).symm }
  have hη (M : SheafOfModules.{u} (R.over U)) (V : C) :
      IsIso ((η.app M).app (op V)) := by
    classical
    let A : (V ⟶ U) → ModuleCat (R.obj.obj (op V)) := extensionByZeroSummands J R U M V
    let B : (V ⟶ U) → AddCommGrpCat.{u} := fun f => (FAb.obj M).obj (op (Over.mk f))
    let H := Discrete.functor A
    let forgetMod := forget₂ (ModuleCat (R.obj.obj (op V))) AddCommGrpCat
    let q := extensionByZeroPresheafSectionIso J R U M V
    let eNat : H ⋙ forgetMod ≅ Discrete.functor B :=
      Discrete.compNatIsoDiscrete A forgetMod ≪≫
        Discrete.natIso (fun i => eqToIso (show forgetMod.obj (A i.as) = B i.as from rfl))
    let e : (∐ B) ≅ forgetMod.obj (∐ A) :=
      (HasColimit.isoOfNatIso eNat).symm ≪≫ (preservesColimitIso forgetMod H).symm
    let μ : (∐ B) ⟶ (Fpres.obj M).obj (op V) := e.hom ≫ forgetMod.map q.inv
    have hμ : IsIso μ := inferInstanceAs (IsIso (e ≪≫ forgetMod.mapIso q.symm).hom)
    let d := Sigma.desc
      (f := B)
      (P := (L.lan.obj (FAb.obj M)).obj (op V))
      (fun f => ((L.lanUnit.app (FAb.obj M)).app (op (Over.mk f))))
    have hd : IsIso d := isIso_lanSigmaDesc U (FAb.obj M) V
    have hcomp : d ≫ (η.app M).app (op V) = μ := by
      apply Sigma.hom_ext
      intro f
      have hdesc : Sigma.ι B f ≫ d =
          (L.lanUnit.app (FAb.obj M)).app (op (Over.mk f)) := Sigma.ι_desc _ f
      have he : Sigma.ι B f ≫ e.hom =
          eNat.inv.app (Discrete.mk f) ≫ forgetMod.map (Sigma.ι A f) := by
        dsimp [e]
        rw [← Category.assoc, HasColimit.isoOfNatIso_ι_inv, Category.assoc,
          ι_preservesColimitIso_inv]
      have hunitMod : Sigma.ι A f ≫ q.inv =
          ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
            (F := Over.forget U) (R := R.obj) (S := (R.over U).obj)
            (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).unit.app M.val).app
              (op (Over.mk f)) :=
        HEq.eq (extensionByZeroPresheafSectionIso_inv_ι J R U M V f)
      have hadj : ((L.lanUnit.app (FAb.obj M)).app (op (Over.mk f))) ≫
          (η.app M).app (op V) = (η₀.app M).app (op (Over.mk f)) := by
        have h' : η₀.app M = adjLan.unit.app (FAb.obj M) ≫ Lpre.map (etaApp M) := by
          calc
            η₀.app M = (adjLan.homEquiv (FAb.obj M) (Fpres.obj M)) (etaApp M) :=
              (Equiv.apply_symm_apply (adjLan.homEquiv (FAb.obj M) (Fpres.obj M))
                (η₀.app M)).symm
            _ = adjLan.unit.app (FAb.obj M) ≫ Lpre.map (etaApp M) := by
              simpa [Lpre] using adjLan.homEquiv_unit (f := etaApp M)
        simpa [Lpre, η, etaApp, adjLan, Functor.lanAdjunction_unit, L] using
          congrArg (fun α => α.app (op (Over.mk f))) h'.symm
      have hη₀ : (η₀.app M).app (op (Over.mk f)) =
          eNat.inv.app (Discrete.mk f) ≫ forgetMod.map
            (((PresheafOfModules.pullbackPushforwardAdjunction.{u}
              (F := Over.forget U) (R := R.obj) (S := (R.over U).obj)
              (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).unit.app M.val).app
                (op (Over.mk f))) := by
        apply AddCommGrpCat.ext
        intro x
        rfl
      have hRHS : Sigma.ι B f ≫ μ =
          eNat.inv.app (Discrete.mk f) ≫ forgetMod.map
            (((PresheafOfModules.pullbackPushforwardAdjunction.{u}
              (F := Over.forget U) (R := R.obj) (S := (R.over U).obj)
              (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).unit.app M.val).app
                (op (Over.mk f))) := by
        have h3 : (eNat.inv.app (Discrete.mk f) ≫ forgetMod.map (Sigma.ι A f)) ≫
              forgetMod.map q.inv =
            eNat.inv.app (Discrete.mk f) ≫ forgetMod.map (Sigma.ι A f ≫ q.inv) := by
          rw [Category.assoc, ← Functor.map_comp]
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (fun x => x ≫ forgetMod.map q.inv) he).trans
            (h3.trans (congrArg
              (fun x => eNat.inv.app (Discrete.mk f) ≫ forgetMod.map x) hunitMod)))
      exact ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun x => x ≫ (η.app M).app (op V)) hdesc).trans
          (hadj.trans hη₀))).trans hRHS.symm
    have : IsIso d := hd
    have hcompIso : IsIso (d ≫ (η.app M).app (op V)) := by
      rw [hcomp]
      exact hμ
    exact IsIso.of_isIso_comp_left d ((η.app M).app (op V))
  let ηIso : FAb ⋙ L.lan ≅ Fmod ⋙ PresheafOfModules.toPresheaf R.obj :=
    NatIso.ofComponents
      (fun M => NatIso.ofComponents
        (fun V => asIso ((η.app M).app V)) (fun f => (η.app M).naturality f))
      (fun f => η.naturality f)
  let leftIso :
      SheafOfModules.pullback.{u} (F := Over.forget U) (S := R.over U)
          (R := R) (𝟙 (R.over U)) ⋙ SheafOfModules.toSheaf R ≅
        FAb ⋙ L.lan ⋙ presheafToSheaf J AddCommGrpCat.{u} :=
    (Functor.isoWhiskerRight
      (SheafOfModules.pullbackIso.{u}
        (F := Over.forget U) (S := R.over U) (R := R) φs)
        (SheafOfModules.toSheaf R)) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft Fmod
        (PresheafOfModules.sheafificationCompToSheaf.{u} (𝟙 R.obj)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ηIso.symm (presheafToSheaf J AddCommGrpCat.{u}) ≪≫
      Functor.associator _ _ _
  let rightIso :
      SheafOfModules.toSheaf (R.over U) ⋙ Q ≅
        FAb ⋙ L.lan ⋙ presheafToSheaf J AddCommGrpCat.{u} := by
    change SheafOfModules.toSheaf (R.over U) ⋙
        (sheafToPresheaf (J.over U) AddCommGrpCat.{u} ⋙
          (L.lan ⋙ presheafToSheaf J AddCommGrpCat.{u})) ≅ _
    exact (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (SheafOfModules.toSheafCompSheafToPresheafIso.{u} (R.over U))
        (L.lan ⋙ presheafToSheaf J AddCommGrpCat.{u})
  exact leftIso ≪≫ rightIso.symm

end Stacks.Sites.ExtensionByZero

-- ===== merged from StacksDraft.Ch18.Sec19.ExtensionByZeroReflectsExactness =====

/-!
# Extension by zero reflects exactness

Let `(C, O)` be a ringed site and `U` an object of `C`. Extension by zero
`j_{U!} : Mod(O_U) ⟶ Mod(O)` along the localization `C/U ⟶ C` is exact, by Stacks 03DJ. This
file proves the converse half of Stacks 0E8G: a complex of `O_U`-modules is exact as soon as
its extension by zero is, so `j_{U!}` *reflects* exactness as well as preserving it.

Reflection comes from faithfulness. The unit of the adjunction `j_{U!} ⊣ j_U^*` is a
monomorphism at every sheaf of modules, hence `j_{U!}` is faithful, and an exact faithful
functor between abelian categories reflects exactness of short complexes
(`CategoryTheory.ShortComplex.exact_map_iff_of_faithful`).

That the unit is a monomorphism is proved in two steps, following the construction of
`j_{U!}` as a presheaf extension followed by sheafification. At the presheaf level the unit at
`G`, evaluated on an object `V ⟶ U` of the slice site, is the inclusion of a summand of the
direct sum computed by Stacks 03DI, hence a split injection. Sheafification is locally
injective, and local injectivity is stable under restriction along the cocontinuous functor
`Over.forget U`, so the composite unit is locally injective on the slice site; its source is a
*sheaf*, hence separated, so local injectivity upgrades to injectivity and therefore to a
monomorphism.

## Main results

* `Stacks.Sites.ExtensionByZero.extensionByZero_exact_iff`: a short complex of sheaves of
  modules on `C/U` is exact if and only if its extension by zero is exact.

## Implementation notes

The complex is represented by a `ShortComplex`. The statement is for an arbitrary sheaf of
rings on a site, which covers the structure sheaf of a ringed site.

The hypothesis that restriction of *presheaves* of modules along `Over.forget U` is a right
adjoint is taken as an instance argument of the auxiliary lemma rather than looked up: the
instance `presheafRestrictionIsRightAdjoint` spells its subject in a form that the
instance discrimination tree does not match against the form
`SheafOfModules.PullbackConstruction.adjunction` asks for, so it has to be supplied into the
local context, where unification is up to definitional unfolding.

## References

* [Stacks Project, Tag 0E8G](https://stacks.math.columbia.edu/tag/0E8G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sites.ExtensionByZero

universe u

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  (R : Sheaf J RingCat.{u}) (U : C)
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The unit of the presheaf extension/restriction adjunction is a monomorphism: on the
sections over an object `V ⟶ U` of the slice site it is the inclusion of the summand of
`∐ extensionByZeroSummands` indexed by that object. -/
private lemma presheafUnit_mono (G : SheafOfModules.{u} (R.over U)) :
    Mono ((PresheafOfModules.pullbackPushforwardAdjunction.{u} (F := Over.forget U)
      (R := R.obj) (S := (R.over U).obj)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).unit.app G.val) := by
  apply PresheafOfModules.mono_of_injective
  intro X
  have hinj : Function.Injective (ConcreteCategory.hom
      (Sigma.ι (extensionByZeroSummands J R U G X.unop.left) X.unop.hom ≫
        (extensionByZeroPresheafSectionIso J R U G X.unop.left).inv)) := by
    apply (ModuleCat.mono_iff_injective _).1
    infer_instance
  rw [sigma_ι_comp_sectionIso_inv J R U G X.unop.left X.unop.hom] at hinj
  exact hinj

/-- The unit of the extension-by-zero/restriction adjunction of *sheaves* of modules is a
monomorphism: the presheaf-level unit is injective and sheafification is locally injective,
which on a separated presheaf is injectivity. -/
private theorem unit_mono
    [(PresheafOfModules.pushforward.{u} (F := Over.forget U) (R := R.obj)
      (S := (R.over U).obj)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).IsRightAdjoint]
    (G : SheafOfModules.{u} (R.over U)) :
    Mono ((SheafOfModules.PullbackConstruction.adjunction.{u}
      (F := Over.forget U) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).unit.app G) := by
  let pAdj := PresheafOfModules.pullbackPushforwardAdjunction.{u} (F := Over.forget U)
    (R := R.obj) (S := (R.over U).obj) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom
  let P := (PresheafOfModules.pullback.{u} (F := Over.forget U) (R := R.obj)
    (S := (R.over U).obj) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom).obj G.val
  let sAdj := PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R.obj)
  let A := SheafOfModules.PullbackConstruction.adjunction.{u}
    (F := Over.forget U) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))
  let push := PresheafOfModules.pushforward.{u} (F := Over.forget U) (R := R.obj)
    (S := (R.over U).obj) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom
  have hform : (SheafOfModules.forget (R.over U)).map (A.unit.app G) =
      pAdj.unit.app G.val ≫ push.map (sAdj.unit.app P) := by
    dsimp [A, P, pAdj, sAdj, push, SheafOfModules.PullbackConstruction.adjunction,
      Adjunction.mkOfHomEquiv]
    rfl
  -- the presheaf-level unit is injective, hence locally injective
  have hp : Presheaf.IsLocallyInjective (J.over U)
      ((PresheafOfModules.toPresheaf (R.over U).obj).map (pAdj.unit.app G.val)) := by
    have hpm : Mono (pAdj.unit.app G.val) := presheafUnit_mono J R U G
    have hm : Mono ((PresheafOfModules.toPresheaf (R.over U).obj).map
        (pAdj.unit.app G.val)) :=
      Functor.map_mono (PresheafOfModules.toPresheaf (R.over U).obj) (pAdj.unit.app G.val)
    exact Presheaf.isLocallyInjective_of_injective _ _ fun X =>
      (AddCommGrpCat.mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 hm X)
  -- the unit of sheafification is locally injective, and restriction to the slice site is
  -- along a cocontinuous functor, so it stays locally injective there
  have hs : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf R.obj).map (sAdj.unit.app P)) := by
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact (J.W_toSheafify P.presheaf).isLocallyInjective
  let ψ := (PresheafOfModules.toPresheaf R.obj).map (sAdj.unit.app P)
  have hs' : Presheaf.IsLocallyInjective (J.over U)
      (Functor.whiskerLeft (Over.forget U).op ψ) :=
    Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U) ψ
  have hpush : (PresheafOfModules.toPresheaf (R.over U).obj).map
      (push.map (sAdj.unit.app P)) = Functor.whiskerLeft (Over.forget U).op ψ := rfl
  have hpushlocal : Presheaf.IsLocallyInjective (J.over U)
      ((PresheafOfModules.toPresheaf (R.over U).obj).map
        (push.map (sAdj.unit.app P))) := by
    rwa [hpush]
  have hcomp : Presheaf.IsLocallyInjective (J.over U)
      ((PresheafOfModules.toPresheaf (R.over U).obj).map
        (pAdj.unit.app G.val ≫ push.map (sAdj.unit.app P))) := by
    have hcomp' : Presheaf.IsLocallyInjective (J.over U)
        ((PresheafOfModules.toPresheaf (R.over U).obj).map (pAdj.unit.app G.val) ≫
          (PresheafOfModules.toPresheaf (R.over U).obj).map
            (push.map (sAdj.unit.app P))) := inferInstance
    simpa only [Functor.map_comp] using hcomp'
  -- the source is a sheaf, hence separated, so local injectivity is injectivity
  let Fsrc := (SheafOfModules.toSheaf (R.over U)).obj G
  let f := (SheafOfModules.toSheaf (R.over U)).map (A.unit.app G)
  let fP := (sheafToPresheaf (J.over U) AddCommGrpCat.{u}).map f
  have hsep : Presieve.IsSeparated (J.over U)
      (Fsrc.obj ⋙ CategoryTheory.forget AddCommGrpCat.{u}) := by
    intro X S hS _ t₁ t₂ h₁ h₂
    exact Fsrc.property.isSeparated X S hS t₁ t₂ fun Y g hg => (h₁ g hg).trans (h₂ g hg).symm
  have hlocalP : Presheaf.IsLocallyInjective (J.over U) fP := by
    show Presheaf.IsLocallyInjective (J.over U)
      ((PresheafOfModules.toPresheaf (R.over U).obj).map
        ((SheafOfModules.forget (R.over U)).map (A.unit.app G)))
    rw [hform]
    exact hcomp
  have hmonoP : Mono fP :=
    (NatTrans.mono_iff_mono_app fP).2 fun X =>
      (AddCommGrpCat.mono_iff_injective _).2
        ((Presheaf.isLocallyInjective_iff_injective_of_separated (J.over U) fP hsep).mp
          hlocalP X)
  exact Functor.mono_of_mono_map (SheafOfModules.toSheaf (R.over U))
    (Functor.mono_of_mono_map _ hmonoP)

/-- **Stacks 0E8G.** Extension by zero from the slice site reflects, as well as preserves,
exactness of complexes of sheaves of modules. -/
@[stacks 0E8G]
theorem extensionByZero_exact_iff
    (S : ShortComplex (SheafOfModules.{u} (R.over U))) :
    (S.map (SheafOfModules.pullback.{u} (F := Over.forget U)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)))).Exact ↔ S.Exact := by
  have := presheafRestrictionIsRightAdjoint J R U
  let F := SheafOfModules.pullback.{u} (F := Over.forget U)
    (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))
  let A := SheafOfModules.PullbackConstruction.adjunction.{u}
    (F := Over.forget U) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))
  have : ∀ X : SheafOfModules.{u} (R.over U), Mono (A.unit.app X) := unit_mono J R U
  have : (SheafOfModules.forget (R.over U) ⋙
      PresheafOfModules.pullback.{u} (F := Over.forget U) (R := R.obj)
        (S := (R.over U).obj) (𝟙 (R.over U) : (R.over U) ⟶ (R.over U)).hom ⋙
      PresheafOfModules.sheafification (R₀ := R.obj) (𝟙 R.obj)).Faithful :=
    A.faithful_L_of_mono_unit_app
  have : F.Faithful := CategoryTheory.Functor.Faithful.of_iso
    (SheafOfModules.pullbackIso (F := Over.forget U)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).symm
  have hpres := (exactFunctor_iff F).mp (extensionByZero_exact J R U)
  have : PreservesFiniteLimits F := hpres.1
  have : PreservesFiniteColimits F := hpres.2
  simpa only [F] using ShortComplex.exact_map_iff_of_faithful S F

end Stacks.Sites.ExtensionByZero
