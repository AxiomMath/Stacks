module

public import Mathlib.CategoryTheory.Limits.Constructions.Filtered
public import Mathlib.CategoryTheory.Monad.Limits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.CoherentModuleFunctors.Extension
public import
 StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsModuleCategories.FiniteSubsetCoproduct

/-!
# Direct sums and extensions of additive functors on coherent modules

Let `X` and `Y` be schemes with `X` Noetherian. A filtered-colimit-preserving extension to the
quasi-coherent modules of an additive functor `Coh(𝒪_X) ⥤ Coh(𝒪_Y)` is itself additive, and it
commutes with arbitrary direct sums.

## Main results

* `AlgebraicGeometry.CoherentModuleFunctors.FilteredColimitExtension.additive`: the extension of
  an additive functor is additive.
* `AlgebraicGeometry.CoherentModuleFunctors.FilteredColimitExtension.preservesCoproducts`: the
  extension preserves coproducts indexed by any type in the scheme universe.

## Implementation notes

The result applies to an arbitrary extension equipped with its filtered-colimit preservation and
its specified identification on the coherent modules, not only to the chosen one. Additivity is
proved first on the coherent modules, where the identification transports it from the original
functor, and then in general by writing a quasi-coherent module as a filtered colimit of coherent
modules, which is possible because `X` is Noetherian, and factoring a pair of morphisms out of
one stage through a single stage of the target. Preservation of direct sums is then the general
fact that an additive functor commuting with filtered colimits commutes with all coproducts, a
coproduct being the filtered colimit of its finite subcoproducts. Only `X` has to be Noetherian;
the category of quasi-coherent modules on `Y` has arbitrary direct sums for every scheme.

## References

* [Stacks Project, Tag 0FZL](https://stacks.math.columbia.edu/tag/0FZL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SheafOfModules (CoherentModules)

universe u

namespace AlgebraicGeometry.CoherentModuleFunctors

/-! ### Additive functors commuting with filtered colimits commute with direct sums -/

section General

universe w

variable {C : Type*} [Category C]

/-- Two morphisms from a finitely presentable object into a filtered colimit factor through one
and the same stage of the colimit. -/
private lemma exists_common_factorisation {J : Type w} [SmallCategory J]
    {B : C} (pres : ColimitPresentation J B) (hJ : IsFiltered J) {Z : C}
    (hZ : IsFinitelyPresentable.{w} Z) (f g : Z ⟶ B) :
    ∃ (k : J) (af ag : Z ⟶ pres.diag.obj k),
      af ≫ pres.ι.app k = f ∧ ag ≫ pres.ι.app k = g := by
  have factor (h : Z ⟶ B) := IsFinitelyPresentable.exists_hom_of_isColimit pres.isColimit h
  obtain ⟨j₁, af₀, hqf⟩ := factor f
  obtain ⟨j₂, ag₀, hqg⟩ := factor g
  obtain ⟨k, hj₁, hj₂, -⟩ := IsFilteredOrEmpty.cocone_objs j₁ j₂
  refine ⟨k, af₀ ≫ pres.diag.map hj₁, ag₀ ≫ pres.diag.map hj₂, ?_, ?_⟩
  · rwa [Category.assoc, pres.w hj₁]
  · rwa [Category.assoc, pres.w hj₂]

variable [Preadditive C] {D : Type*} [Category D] [Preadditive D]

omit [Preadditive C] [Preadditive D] in
/-- The comparison isomorphism for a preserved coproduct, read off on the summand inclusions:
the image of `Sigma.ι f j` followed by `PreservesCoproduct.iso G f` is `Sigma.ι (G ∘ f) j`. -/
private lemma map_ι_comp_preservesCoproduct_iso_hom {J : Type*} (G : C ⥤ D) (f : J → C)
    [HasCoproduct f] [HasCoproduct fun j => G.obj (f j)]
    [PreservesColimit (Discrete.functor f) G] (j : J) :
    G.map (Sigma.ι f j) ≫ (PreservesCoproduct.iso G f).hom =
      Sigma.ι (fun x => G.obj (f x)) j := by
  have h : (PreservesCoproduct.iso G f).hom = inv (sigmaComparison G f) :=
    (IsIso.inv_eq_of_hom_inv_id (PreservesCoproduct.iso G f).inv_hom_id).symm
  rw [h, map_ι_comp_inv_sigmaComparison]

/-- A functor whose restriction along a fully faithful additive functor is identified with an
additive functor is additive on the morphisms in the image of that functor. -/
private lemma map_add_of_comp_iso {E : Type*} [Category E] [Preadditive E]
    {ι : C ⥤ D} [ι.Full] [ι.Faithful] [ι.Additive] {G : D ⥤ E} {H : C ⥤ E} [H.Additive]
    (θ : ι ⋙ G ≅ H) {A B : C} (f g : ι.obj A ⟶ ι.obj B) :
    G.map (f + g) = G.map f + G.map g := by
  obtain ⟨f', rfl⟩ := ι.map_surjective f
  obtain ⟨g', rfl⟩ := ι.map_surjective g
  have key (h : A ⟶ B) : G.map (ι.map h) = θ.hom.app A ≫ H.map h ≫ θ.inv.app B := by
    rw [← θ.hom.naturality_assoc]
    simp
  rw [← ι.map_add, key (f' + g'), key f', key g', H.map_add, Preadditive.add_comp,
    Preadditive.comp_add]

/-- Additivity of a functor at a pair of morphisms out of an object follows from additivity at
a pair of morphisms through which they factor. -/
private lemma map_comp_add_of_factorisation {G : C ⥤ D} {Z A B W : C} (ix : Z ⟶ A)
    {f g : A ⟶ B} {af ag : Z ⟶ W} {y : W ⟶ B}
    (haf : af ≫ y = ix ≫ f) (hag : ag ≫ y = ix ≫ g)
    (hstage : G.map (af + ag) = G.map af + G.map ag) :
    G.map ix ≫ G.map (f + g) = G.map ix ≫ (G.map f + G.map g) := by
  have hfg : ix ≫ (f + g) = (af + ag) ≫ y := by
    rw [Preadditive.comp_add, Preadditive.add_comp, haf, hag]
  rw [← Functor.map_comp, hfg, Functor.map_comp, hstage, Preadditive.add_comp,
    ← Functor.map_comp, ← Functor.map_comp, haf, hag, Functor.map_comp, Functor.map_comp,
    ← Preadditive.comp_add]

/-- Applying an additive functor to the finite subcoproducts of a discrete diagram agrees with
taking the finite subcoproducts of the image diagram. -/
private noncomputable def liftToFinsetObjCompIso [HasFiniteBiproducts C] [HasFiniteBiproducts D]
    (G : C ⥤ D) [G.Additive] {J : Type w} (K : Discrete J ⥤ C) :
    CoproductsFromFiniteFiltered.liftToFinsetObj K ⋙ G ≅
      CoproductsFromFiniteFiltered.liftToFinsetObj (K ⋙ G) :=
  NatIso.ofComponents
    (fun S => PreservesCoproduct.iso G (fun x : S => K.obj x.val)) (by
      intro S T h
      refine (isColimitOfHasCoproductOfPreservesColimit G
        (fun y : S => K.obj y.val)).hom_ext fun j => ?_
      obtain ⟨x⟩ := j
      change @Eq (G.obj (K.obj x.val) ⟶ ∐ fun y : T => G.obj (K.obj y.val))
        (G.map (Sigma.ι (fun y : S => K.obj y.val) x) ≫
          G.map (Sigma.desc fun y : S =>
              Sigma.ι (fun z : T => K.obj z.val) ⟨y.val, h.down.down y.2⟩) ≫
            (PreservesCoproduct.iso G (fun y : T => K.obj y.val)).hom)
        (G.map (Sigma.ι (fun y : S => K.obj y.val) x) ≫
          (PreservesCoproduct.iso G (fun y : S => K.obj y.val)).hom ≫
            Sigma.desc fun y : S =>
              Sigma.ι (fun z : T => G.obj (K.obj z.val)) ⟨y.val, h.down.down y.2⟩)
      simp only [← Category.assoc, ← G.map_comp, Sigma.ι_desc,
        map_ι_comp_preservesCoproduct_iso_hom])

/-- An additive functor commuting with filtered colimits preserves the coproduct of a family. -/
private lemma preservesColimit_discrete_functor_of_additive
    [HasFiniteBiproducts C] [HasFiniteBiproducts D]
    (G : C ⥤ D) [G.Additive] [PreservesFilteredColimitsOfSize.{w, w} G] {J : Type w}
    [HasColimitsOfShape (Discrete J) C] [HasColimitsOfShape (Finset (Discrete J)) C]
    (f : J → C) : PreservesColimit (Discrete.functor f) G := by
  classical
  let K : Discrete J ⥤ C := Discrete.functor f
  let K' : Discrete J ⥤ D := K ⋙ G
  let Dg' := CoproductsFromFiniteFiltered.liftToFinsetObj K'
  let α := liftToFinsetObjCompIso G K
  let csrc := CoproductsFromFiniteFiltered.finiteSubcoproductsCocone f
  have : PreservesColimitsOfShape (Finset (Discrete J)) G :=
    PreservesFilteredColimitsOfSize.preserves_filtered_colimits (Finset (Discrete J))
  let cG := G.mapCocone csrc
  let cD : Cocone Dg' := (Cocone.precompose α.inv).obj cG
  have hcD : IsColimit cD := (IsColimit.precomposeHomEquiv α.symm cG).2
    (isColimitOfPreserves G (CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone f))
  have : HasColimit Dg' := ⟨⟨cD, hcD⟩⟩
  let ctgt := Limits.finiteSubsetCoproductCocone K'
  let cCoprod : Cocone K := Cofan.mk (∐ f) (Sigma.ι f)
  have hmap : IsColimit (G.mapCocone cCoprod) := by
    let e := hcD.coconePointUniqueUpToIso (colimit.isColimit Dg')
    apply IsColimit.ofIsoColimit ctgt.isColimit
    refine Cocone.ext (show ctgt.cocone.pt ≅ (G.mapCocone cCoprod).pt from ?_) ?_
    · simpa [ctgt, Limits.finiteSubsetCoproductCocone,
        Limits.finiteSubsetCoconeOfColimit, Dg', cCoprod, cD, cG, csrc,
        CoproductsFromFiniteFiltered.finiteSubcoproductsCocone] using e.symm
    intro j
    have hleg : colimit.ι Dg' {j} ≫ e.inv = cD.ι.app {j} :=
      hcD.comp_coconePointUniqueUpToIso_inv (colimit.isColimit Dg') {j}
    show (Sigma.ι (fun x : ({j} : Finset (Discrete J)) => K'.obj x.val)
        ⟨j, Finset.mem_singleton_self j⟩ ≫ colimit.ι Dg' {j}) ≫ e.inv =
      G.map (Sigma.ι f j.as)
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun z : Dg'.obj {j} ⟶ cD.pt =>
      Sigma.ι (fun x : ({j} : Finset (Discrete J)) => K'.obj x.val)
        ⟨j, Finset.mem_singleton_self j⟩ ≫ z) hleg).trans ?_
    show @Eq (G.obj (f j.as) ⟶ G.obj (∐ f))
      (Sigma.ι (fun x : ({j} : Finset (Discrete J)) => G.obj (K.obj x.val))
          ⟨j, Finset.mem_singleton_self j⟩ ≫
        sigmaComparison G (fun x : ({j} : Finset (Discrete J)) => K.obj x.val) ≫
          G.map (Sigma.desc fun s : ({j} : Finset (Discrete J)) => Sigma.ι f s.val.as))
      (G.map (Sigma.ι f j.as))
    rw [← Category.assoc, ι_comp_sigmaComparison, ← G.map_comp, Sigma.ι_desc]
  exact Limits.preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct f) hmap

/-- **An additive functor commuting with filtered colimits commutes with arbitrary direct
sums**: a coproduct is the filtered colimit of its finite subcoproducts, and those are
biproducts, which an additive functor preserves. -/
private lemma preservesColimitsOfShape_discrete_of_additive
    [HasFiniteBiproducts C] [HasFiniteBiproducts D]
    (G : C ⥤ D) [G.Additive] [PreservesFilteredColimitsOfSize.{w, w} G] (J : Type w)
    [HasColimitsOfShape (Discrete J) C] [HasColimitsOfShape (Finset (Discrete J)) C] :
    PreservesColimitsOfShape (Discrete J) G :=
  have := preservesColimit_discrete_functor_of_additive G (J := J)
  Limits.preservesColimitsOfShape_of_discrete G

end General

/-! ### Additivity and direct sums for an extension -/

section Additive

variable {X Y : Scheme.{u}} [IsNoetherian X]
  {F : CoherentModules X.ringCatSheaf ⥤ CoherentModules Y.ringCatSheaf} [F.Additive]

/-- The inclusion `Coh(𝒪_X) ⥤ QCoh(𝒪_X)` is additive: it leaves morphisms of `𝒪_X`-modules
unchanged. -/
private instance additive_coherentToQuasicoherent (Z : Scheme.{u}) :
    (coherentToQuasicoherent Z).Additive :=
  ⟨ObjectProperty.hom_ext _ rfl⟩

omit [IsNoetherian X] in
/-- An extension of an additive functor is additive on the coherent modules: there the
identification with the original functor transports additivity. -/
private lemma extension_map_add_of_isCoherent (E : FilteredColimitExtension X Y F)
    {A B : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory}
    (hA : A.obj.IsCoherent) (hB : B.obj.IsCoherent) (f g : A ⟶ B) :
    E.functor.map (f + g) = E.functor.map f + E.functor.map g :=
  map_add_of_comp_iso E.iso (A := ⟨A.obj, hA⟩) (B := ⟨B.obj, hB⟩) f g

/-- At a coherent object mapping into the source, the extension is additive: the two morphisms
factor through a single coherent stage of a filtered presentation of the target, and there
additivity is already known. -/
private lemma extension_map_add_at_stage (E : FilteredColimitExtension X Y F)
    {A B : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory} (f g : A ⟶ B)
    {JB : Type u} [SmallCategory JB] (presB : ColimitPresentation JB B)
    (hfiltB : IsFiltered JB) (hcohB : ∀ j, coherentProperty X (presB.diag.obj j))
    {Z : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory}
    (hZ : coherentProperty X Z) (ix : Z ⟶ A) :
    E.functor.map ix ≫ E.functor.map (f + g) =
      E.functor.map ix ≫ (E.functor.map f + E.functor.map g) := by
  obtain ⟨k, af, ag, haf, hag⟩ := exists_common_factorisation presB hfiltB
    (isFinitelyPresentable_of_isCoherent X Z hZ) (ix ≫ f) (ix ≫ g)
  exact map_comp_add_of_factorisation ix haf hag
    (extension_map_add_of_isCoherent E hZ (hcohB k) af ag)

/-- **The extension of an additive functor on coherent modules is additive.** A quasi-coherent
module on a Noetherian scheme is a filtered colimit of coherent ones whose stages are finitely
presentable, and the extension commutes with that colimit. -/
lemma FilteredColimitExtension.additive (E : FilteredColimitExtension X Y F) :
    E.functor.Additive := by
  refine ⟨fun {A B f g} => ?_⟩
  obtain ⟨JA, _, _, presA, hcohA⟩ := coherentProperty_ind X A
  obtain ⟨JB, _, filtB, presB, hcohB⟩ := coherentProperty_ind X B
  exact (isColimitOfPreserves E.functor presA.isColimit).hom_ext fun i =>
    extension_map_add_at_stage E f g presB filtB hcohB (hcohA i) (presA.ι.app i)

/-- The category of quasi-coherent modules on a scheme has finite biproducts, being abelian. -/
lemma hasFiniteBiproducts_quasicoherent (Z : Scheme.{u}) :
    HasFiniteBiproducts (SheafOfModules.isQuasicoherent Z.ringCatSheaf).FullSubcategory :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The category of quasi-coherent modules on a scheme has all colimits of the scheme's size:
the inclusion into all modules is coreflective. -/
lemma hasColimitsOfSize_quasicoherent (Z : Scheme.{u}) :
    HasColimitsOfSize.{u, u}
      (SheafOfModules.isQuasicoherent Z.ringCatSheaf).FullSubcategory :=
  have := quasicoherentInclusion_isLeftAdjoint Z
  have : Coreflective (SheafOfModules.isQuasicoherent Z.ringCatSheaf).ι :=
    { toFull := inferInstance
      toFaithful := inferInstance
      R := (SheafOfModules.isQuasicoherent Z.ringCatSheaf).ι.rightAdjoint
      adj := Adjunction.ofIsLeftAdjoint (SheafOfModules.isQuasicoherent Z.ringCatSheaf).ι }
  hasColimits_of_coreflective (SheafOfModules.isQuasicoherent Z.ringCatSheaf).ι

/-- **Stacks Project, Tag 0FZL.** An extension of an additive functor on coherent modules
commutes with arbitrary direct sums of quasi-coherent modules. -/
@[stacks 0FZL "direct_sums"]
lemma FilteredColimitExtension.preservesCoproducts (E : FilteredColimitExtension X Y F)
    (J : Type u) : PreservesColimitsOfShape (Discrete J) E.functor :=
  have : E.functor.Additive := E.additive
  have := hasColimitsOfSize_quasicoherent X
  have := hasColimitsOfSize_quasicoherent Y
  have := hasFiniteBiproducts_quasicoherent X
  have := hasFiniteBiproducts_quasicoherent Y
  preservesColimitsOfShape_discrete_of_additive E.functor J

end Additive

end AlgebraicGeometry.CoherentModuleFunctors
