module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.LiftToFinset
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsModuleCategories.Extension
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsModuleCategories.FiniteSubsetCoproduct
public import StacksCore.Tactic.StacksAttribute

/-!
# Additivity of the extension from finitely presented modules

Let `A` be a commutative ring and let `B` be an additive category. An additive functor from
finitely presented `A`-modules extends, by filtered colimits, to an additive functor on all
`A`-modules, and this extension commutes with arbitrary direct sums.

## Main results

* `ModuleCat.filteredColimitExtension_additive`: the extended functor is additive.
* `ModuleCat.filteredColimitExtension_preservesCoproducts`: it commutes with arbitrary direct
  sums.
* `ModuleCat.extension_map_add` and `ModuleCat.extension_preserves_discrete_coproducts` are the
  same statements for an arbitrary, not necessarily commutative, ring.

## Implementation notes

The results are stated for any filtered-colimit extension equipped with its specified
identification on finitely presented modules; in particular they apply to the extension chosen
in `ModuleCat.filteredColimitExtension`. Additive categories are represented by a preadditive
structure together with finite biproducts. Commutation with direct sums is expressed as
preservation of colimits of discrete diagrams, so it includes the canonical comparison map and
its naturality.

Additivity is checked on finitely presented modules first and then transported to an arbitrary
pair of modules by writing each as a filtered colimit of finitely presented ones and using that
a finitely presented module is categorically compact, so that each stage map factors through a
stage of the target.

## References

* [Stacks Project, Tag 0GNK](https://stacks.math.columbia.edu/tag/0GNK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w x z

namespace ModuleCat

section Ring

variable (A : Type u) [Ring A]
variable {B : Type w} [Category.{x} B] [Preadditive B]
variable {F : CategoryTheory.Functor (FinitelyPresentedModuleCat.{u, max u v} A) B}

/-- On finitely presented modules the extension preserves sums of morphisms, because there it
agrees with the given additive functor. -/
public lemma extension_map_add_on_finitelyPresented
    (E : FilteredColimitExtension A F) [F.Additive]
    {X Y : ModuleCat.{max u v} A}
    (hX : Module.FinitePresentation A X) (hY : Module.FinitePresentation A Y)
    (f g : X ⟶ Y) :
    E.functor.map (f + g) = E.functor.map f + E.functor.map g := by
  let X' : FinitelyPresentedModuleCat.{u, max u v} A := ⟨X, hX⟩
  let Y' : FinitelyPresentedModuleCat.{u, max u v} A := ⟨Y, hY⟩
  let f' : X' ⟶ Y' := ObjectProperty.homMk f
  let g' : X' ⟶ Y' := ObjectProperty.homMk g
  have : IsIso (E.iso.hom.app X') := NatIso.isIso_app_of_isIso _ _
  have : IsIso (E.iso.hom.app Y') := NatIso.isIso_app_of_isIso _ _
  have nat (h : X' ⟶ Y') :
      E.functor.map h.hom ≫ E.iso.hom.app Y' =
        E.iso.hom.app X' ≫ F.map h := by
    simpa only [Functor.comp_map, Functor.comp_obj, ObjectProperty.ι_map,
      ObjectProperty.ι_obj] using E.iso.hom.naturality h
  apply (cancel_mono (E.iso.hom.app Y')).1
  calc
    E.functor.map (f + g) ≫ E.iso.hom.app Y' =
        E.iso.hom.app X' ≫ F.map (f' + g') := by
      simpa only [show (f' + g').hom = f + g from rfl] using nat (f' + g')
    _ = E.iso.hom.app X' ≫ (F.map f' + F.map g') := by simp only [Functor.map_add]
    _ = (E.functor.map f + E.functor.map g) ≫ E.iso.hom.app Y' := by
      rw [Preadditive.comp_add, Preadditive.add_comp, ← nat f', ← nat g']
      rfl

/-- The extension preserves sums of morphisms. -/
public lemma extension_map_add
    (E : FilteredColimitExtension A F) [F.Additive]
    {X Y : ModuleCat.{max u v} A} (f g : X ⟶ Y) :
    E.functor.map (f + g) = E.functor.map f + E.functor.map g := by
  classical
  obtain ⟨I, hI, hIf, cX, hPX⟩ := ind_finitelyPresentedModule A X
  obtain ⟨J, hJ, hJf, cY, hPY⟩ := ind_finitelyPresentedModule A Y
  let : SmallCategory I := hI
  let : IsFiltered I := hIf
  let : SmallCategory J := hJ
  let : IsFiltered J := hJf
  let : PreservesColimitsOfShape I E.functor :=
    PreservesFilteredColimitsOfSize.preserves_filtered_colimits I
  have hcX := isColimitOfPreserves E.functor cX.isColimit
  apply hcX.hom_ext
  intro i
  let ix : cX.diag.obj i ⟶ X := cX.ι.app i
  let : Module.FinitePresentation A (cX.diag.obj i) := hPX i
  let : IsFinitelyPresentable.{max u v} (cX.diag.obj i) :=
    finitePresentation_isFinitelyPresentable A (cX.diag.obj i) (hPX i)
  have lift (h : X ⟶ Y) :
      ∃ (j : J) (a : cX.diag.obj i ⟶ cY.diag.obj j), a ≫ cY.ι.app j = ix ≫ h := by
    obtain ⟨j, a, ha⟩ := IsFinitelyPresentable.exists_hom_of_isColimit cY.isColimit (ix ≫ h)
    exact ⟨j, a, by simpa [ix] using ha⟩
  obtain ⟨k, af, ag, haf, hag⟩ : ∃ (k : J) (af ag : cX.diag.obj i ⟶ cY.diag.obj k),
      af ≫ cY.ι.app k = ix ≫ f ∧ ag ≫ cY.ι.app k = ix ≫ g := by
    obtain ⟨jf, af, hqf⟩ := lift f
    obtain ⟨jg, ag, hqg⟩ := lift g
    obtain ⟨k, hjf, hjg, _⟩ := IsFilteredOrEmpty.cocone_objs jf jg
    exact ⟨k, af ≫ cY.diag.map hjf, ag ≫ cY.diag.map hjg,
      by rw [Category.assoc, cY.w, hqf], by rw [Category.assoc, cY.w, hqg]⟩
  have hsum : ix ≫ (f + g) = (af + ag) ≫ cY.ι.app k := by
    rw [Preadditive.comp_add, ← haf, ← hag, Preadditive.add_comp]
  calc
    E.functor.map ix ≫ E.functor.map (f + g) = E.functor.map ((af + ag) ≫ cY.ι.app k) := by
      rw [← Functor.map_comp, hsum]
    _ = E.functor.map (ix ≫ f) + E.functor.map (ix ≫ g) := by
      rw [Functor.map_comp, extension_map_add_on_finitelyPresented A E (hPX i) (hPY k),
        Preadditive.add_comp, ← Functor.map_comp, ← Functor.map_comp, haf, hag]
    _ = E.functor.map ix ≫ (E.functor.map f + E.functor.map g) := by
      rw [Preadditive.comp_add, Functor.map_comp, Functor.map_comp]

variable [HasFiniteBiproducts B]

/-- The extension commutes with coproducts of a family indexed by any type of the size of the
module category: the coproduct is the filtered colimit of its finite subcoproducts, and the
extension commutes with both. -/
public lemma extension_preserves_discrete_coproducts
    (E : FilteredColimitExtension A F) [F.Additive]
    (J : Type (max u v)) :
    PreservesColimitsOfShape (Discrete J) E.functor := by
  have : E.functor.Additive := ⟨extension_map_add A E _ _⟩
  have : ∀ (f : J → ModuleCat.{max u v} A),
      PreservesColimit (Discrete.functor f) E.functor := by
    intro f
    classical
    let K : Discrete J ⥤ ModuleCat.{max u v} A := Discrete.functor f
    let K' : Discrete J ⥤ B := K ⋙ E.functor
    let D := CoproductsFromFiniteFiltered.liftToFinsetObj K
    let D' := CoproductsFromFiniteFiltered.liftToFinsetObj K'
    -- Stated in the direction whose components are `sigmaComparison`: `Sigma.hom_ext` then
    -- applies on the nose, where in the other direction the source of the naturality square is
    -- not a coproduct and the comparison map has to be cancelled off first.
    let α : D ⋙ E.functor ≅ D' := (NatIso.ofComponents
      (fun S => (PreservesCoproduct.iso E.functor (fun x : S => K.obj x.val)).symm) (by
      intro S T h
      -- `liftToFinsetObj` is built from `HasColimit.getColimitCocone`, which is not exposed, so
      -- the objects of the square have to be named in the coproduct form the lemmas expect.
      change @Eq ((∐ fun x : S => E.functor.obj (K.obj x.val)) ⟶
          E.functor.obj (∐ fun x : T => K.obj x.val))
        ((Sigma.desc fun y : S => Sigma.ι (fun x : T => E.functor.obj (K.obj x.val))
            ⟨y.1, h.down.down y.2⟩) ≫
          sigmaComparison E.functor (fun x : T => K.obj x.val))
        (sigmaComparison E.functor (fun x : S => K.obj x.val) ≫
          E.functor.map (Sigma.desc fun y : S => Sigma.ι (fun x : T => K.obj x.val)
            ⟨y.1, h.down.down y.2⟩))
      ext j
      rw [Sigma.ι_comp_desc_assoc, ι_comp_sigmaComparison, ι_comp_sigmaComparison_assoc,
        ← E.functor.map_comp, Sigma.ι_comp_desc])).symm
    let csrc := CoproductsFromFiniteFiltered.finiteSubcoproductsCocone f
    have : PreservesColimitsOfShape (Finset (Discrete J)) E.functor :=
      PreservesFilteredColimitsOfSize.preserves_filtered_colimits (Finset (Discrete J))
    let cE := E.functor.mapCocone csrc
    let cD : Cocone D' := (Cocone.precompose α.inv).obj cE
    have hcD : IsColimit cD := (IsColimit.precomposeHomEquiv α.symm cE).2
      (isColimitOfPreserves E.functor
        (CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone f))
    have : HasColimit D' := ⟨⟨cD, hcD⟩⟩
    let ctgt := finiteSubsetCoproductCocone K'
    let cCoprod : Cocone K := Cofan.mk (∐ f) (Sigma.ι f)
    have hmap : IsColimit (E.functor.mapCocone cCoprod) := by
      let e := hcD.coconePointUniqueUpToIso (colimit.isColimit D')
      apply IsColimit.ofIsoColimit ctgt.isColimit
      refine Cocone.ext (show ctgt.cocone.pt ≅ (E.functor.mapCocone cCoprod).pt from ?_) ?_
      · simpa [ctgt, finiteSubsetCoproductCocone, finiteSubsetCoconeOfColimit, D', cCoprod,
          cD, cE, csrc, CoproductsFromFiniteFiltered.finiteSubcoproductsCocone] using e.symm
      intro j
      have hleg : colimit.ι D' {j} ≫ e.inv = cD.ι.app {j} :=
        IsColimit.comp_coconePointUniqueUpToIso_inv hcD (colimit.isColimit D') {j}
      change (Sigma.ι (fun x : ({j} : Finset (Discrete J)) => K'.obj x.val)
          ⟨j, Finset.mem_singleton_self j⟩ ≫ colimit.ι D' {j}) ≫ e.inv =
        E.functor.map (Sigma.ι f j.as)
      refine (Category.assoc _ _ _).trans ((congrArg _ hleg).trans ?_)
      simp only [cD, cE, csrc, α, Cocone.precompose_obj_ι, NatTrans.comp_app,
        Functor.mapCocone_ι_app, CoproductsFromFiniteFiltered.finiteSubcoproductsCocone, K, K']
      -- `α.inv.app {j}` is the comparison map `sigmaComparison`; the remaining steps are applied
      -- as terms, since the objects of `D'` are coproducts only up to the unexposed
      -- `HasColimit.getColimitCocone`.
      refine (ι_comp_sigmaComparison_assoc E.functor
        (fun x : ({j} : Finset (Discrete J)) => f x.val.as) _ _).trans ?_
      refine (E.functor.map_comp _ _).symm.trans ?_
      exact congrArg E.functor.map (Sigma.ι_comp_desc _ _)
    exact Limits.preservesColimit_of_preserves_colimit_cocone
      (coproductIsCoproduct f) hmap
  exact Limits.preservesColimitsOfShape_of_discrete E.functor

end Ring

section CommRing

variable (A : Type u) [CommRing A]
variable {B : Type w} [Category.{x} B] [Preadditive B] [HasFiniteBiproducts B]
variable {F : CategoryTheory.Functor (FinitelyPresentedModuleCat.{u, max u v} A) B}

omit [HasFiniteBiproducts B] in
/-- A filtered-colimit-preserving extension of an additive functor from finitely presented
modules is additive. -/
@[stacks 0GNK "additivity"]
public lemma filteredColimitExtension_additive
    (E : FilteredColimitExtension A F) [F.Additive] :
    E.functor.Additive := ⟨extension_map_add A E _ _⟩

/-- A filtered-colimit-preserving extension of an additive functor from finitely presented
modules preserves arbitrary direct sums. -/
@[stacks 0GNK "arbitrary direct sums"]
public lemma filteredColimitExtension_preservesCoproducts
    (E : FilteredColimitExtension A F) [F.Additive]
    (J : Type (max u v)) :
    PreservesColimitsOfShape (Discrete J) E.functor :=
  extension_preserves_discrete_coproducts A E J

end CommRing

end ModuleCat
