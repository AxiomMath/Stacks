module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageRestrictScalars
public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.Cotangent.SheavesOfRings.InverseImageDerivationTransport

/-!
# The inverse image of the cotangent complex

Let `f : Sh(C) ⟶ Sh(D)` be a morphism of topoi and `a : A ⟶ B` a homomorphism of sheaves of
commutative rings on `D`. The inverse image of the cotangent complex of `a` is the cotangent
complex of `f⁻¹a`: `f⁻¹L_{B/A} = L_{f⁻¹B/f⁻¹A}`.

On the algebra side, `CategoryTheory.Sheaf.standardResolutionInverseImageIso` identifies the
inverse image of the standard resolution of `a` with the standard resolution of `f⁻¹a`. On the
module side, `Stacks.Sheaves.RingedToposModules.inverseImageDerivationEquiv` transposes derivations
along `f⁻¹ ⊣ f_*`. Together, the inverse image of the base-changed simplicial module
`Ω_{P_•/A} ⊗_{P_•} B` corepresents the `f⁻¹A`-derivations of the standard resolution of `f⁻¹a`,
degreewise and compatibly with the simplex maps; that is, it is a
`CategoryTheory.Sheaf.CotangentSimplicialModuleData` for `f⁻¹a`. The uniqueness of such a datum
then identifies its complex with `CategoryTheory.Sheaf.cotangentComplex`.

## Main definitions

* `PresheafOfModules.Derivation.postcompEquiv` transports derivations along an isomorphism of
  the coefficient presheaf of modules.
* `Stacks.Sheaves.RingedToposModules.restrictScalarsDerivationCongr` transports derivations
  along an equality of the morphism of sheaves of rings used to restrict the scalars.
* `CategoryTheory.Sheaf.inverseImageCotangentDerivationEquiv` is the corepresentation: a
  morphism out of the inverse image of `Ω_{P_n/A} ⊗_{P_n} B` is an `f⁻¹A`-derivation of the
  degree-`n` term of the standard resolution of `f⁻¹a`.
* `CategoryTheory.Sheaf.inverseImageCotangentData` is the resulting datum for `f⁻¹a`.

## Main results

* `CategoryTheory.Sheaf.inverseImageCotangentComplexIso`: the inverse image of the cotangent
  complex of `a` is the cotangent complex of `f⁻¹a`.

## Implementation notes

The corepresentation is a composition of five bijections: the hom-set bijection of Stacks 03D3,
the corepresentation of the derivations of `a`, the identification of the direct image of a
restriction of scalars with the restriction of scalars of the direct image, the transposition of
derivations, and the transport along the degreewise comparison of the two standard resolutions.
The junction of the last two is not definitional: the transposition produces a module whose
scalars are restricted along `f⁻¹` of the underlying morphism of sheaves of rings, while the
transport needs them restricted along the underlying morphism of `f⁻¹` of the morphism of
sheaves of commutative rings. These two morphisms agree by
`Stacks.Sheaves.ToposPullback.forgetCommRingSheaf_map_pullbackCommRingSheafMap`, which goes
through full faithfulness and is not reflexivity; `restrictScalarsDerivationCongr` is the
abstract transport along such an equality, proved by substituting the equality, so that the two
derivations have the same underlying morphism of sheaves of sets by reflexivity.

The two sites, their morphism universes and the two universes of sections all vary
independently, as in `CategoryTheory.Sheaf.cotangentComplex`; every term in the second half of
this file therefore carries an explicit universe list.

## References

* [Stacks Project, Tag 08SV](https://stacks.math.columbia.edu/tag/08SV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace PresheafOfModules.Derivation

universe v u v₂ u₂

variable {D : Type u₂} [Category.{v₂} D] {S R : Dᵒᵖ ⥤ CommRingCat.{u}}
  {M N P : PresheafOfModules.{v} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})} {φ : S ⟶ R}

/-- Postcomposing a derivation twice is postcomposing by the composition. -/
lemma postcomp_postcomp (DD : PresheafOfModulesOfCommRing.Derivation' M φ) (α : M ⟶ N)
    (β : N ⟶ P) :
    (DD.postcomp α).postcomp β = DD.postcomp (α ≫ β) := rfl

/-- Derivations transport along an isomorphism of the coefficient presheaf of modules: an
isomorphism and its inverse postcompose to mutually inverse maps on derivations. -/
noncomputable def postcompEquiv (e : M ≅ N) :
    PresheafOfModulesOfCommRing.Derivation' M φ ≃ PresheafOfModulesOfCommRing.Derivation' N φ where
  toFun DD := DD.postcomp e.hom
  invFun DD := DD.postcomp e.inv
  left_inv DD :=
    PresheafOfModulesOfCommRing.Derivation.ext (funext fun X ↦ AddMonoidHom.ext fun x ↦ by
      have h : (e.hom ≫ e.inv).app X = 𝟙 (M.obj X) := by rw [e.hom_inv_id]; rfl
      exact ConcreteCategory.congr_hom h (DD.d x))
  right_inv DD :=
    PresheafOfModulesOfCommRing.Derivation.ext (funext fun X ↦ AddMonoidHom.ext fun x ↦ by
      have h : (e.inv ≫ e.hom).app X = 𝟙 (N.obj X) := by rw [e.inv_hom_id]; rfl
      exact ConcreteCategory.congr_hom h (DD.d x))

/-- The equivalence `postcompEquiv e` sends a derivation to its postcomposition with `e.hom`. -/
@[simp]
lemma postcompEquiv_apply (e : M ≅ N) (DD : PresheafOfModulesOfCommRing.Derivation' M φ) :
    postcompEquiv e DD = DD.postcomp e.hom := rfl

end PresheafOfModules.Derivation

namespace Stacks.Sheaves.RingedToposModules

open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

/-! ## Transport of derivations along an equality of restriction morphisms -/

section RestrictCongr

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  {P : Sheaf J CommRingCat.{w}} {R : Sheaf J RingCat.{w}}

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The morphism of underlying sheaves of sets of a composition of morphisms of sheaves of
commutative rings is the composition of the two morphisms of underlying sheaves of sets. -/
lemma commRingSetHom_comp {O₁ O₂ O₃ : Sheaf J CommRingCat.{w}} (α : O₁ ⟶ O₂) (β : O₂ ⟶ O₃) :
    commRingSetHom.{w, v, u} (α ≫ β) =
      commRingSetHom.{w, v, u} α ≫ commRingSetHom.{w, v, u} β :=
  (congrArg (sheafCompose J (forget RingCat.{w})).map
      ((Stacks.forgetCommRingSheaf.{v, u, w} J).map_comp α β)).trans
    ((sheafCompose J (forget RingCat.{w})).map_comp _ _)

/-- Two equal morphisms of sheaves of rings give the same derivations after restriction of
scalars. -/
noncomputable def restrictScalarsDerivationCongr
    (M : SheafOfModules.{w} R) {u u' : (Stacks.forgetCommRingSheaf.{v, u, w} J).obj P ⟶ R}
    (h : u = u') {S : Sheaf J CommRingCat.{w}} (b : S ⟶ P) :
    PresheafOfModulesOfCommRing.Derivation' ((SheafOfModules.restrictScalars u).obj M).val b.hom ≃
      PresheafOfModulesOfCommRing.Derivation' ((SheafOfModules.restrictScalars u').obj M).val
        b.hom := by
  subst h
  exact Equiv.refl _

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The transport along an equality of restriction morphisms does not change the values of a
derivation on sections. -/
@[simp]
lemma restrictScalarsDerivationCongr_d
    (M : SheafOfModules.{w} R) {u u' : (Stacks.forgetCommRingSheaf.{v, u, w} J).obj P ⟶ R}
    (h : u = u') {S : Sheaf J CommRingCat.{w}} (b : S ⟶ P)
    (DD : PresheafOfModulesOfCommRing.Derivation' ((SheafOfModules.restrictScalars u).obj M).val
      b.hom) {X : Cᵒᵖ}
    (z : P.obj.obj X) :
    (restrictScalarsDerivationCongr M h b DD).d z = DD.d z := by
  subst h
  rfl

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The transport along an equality of restriction morphisms commutes with postcomposition by a
morphism of the coefficient module. -/
lemma restrictScalarsDerivationCongr_postcomp
    {M N : SheafOfModules.{w} R} (k : M ⟶ N)
    {u u' : (Stacks.forgetCommRingSheaf.{v, u, w} J).obj P ⟶ R}
    (h : u = u') {S : Sheaf J CommRingCat.{w}} (b : S ⟶ P)
    (DD : PresheafOfModulesOfCommRing.Derivation' ((SheafOfModules.restrictScalars u).obj M).val
      b.hom) :
    restrictScalarsDerivationCongr N h b
        (DD.postcomp ((SheafOfModules.restrictScalars u).map k).val) =
      (restrictScalarsDerivationCongr M h b DD).postcomp
        ((SheafOfModules.restrictScalars u').map k).val := by
  subst h
  rfl

/-- The morphism of underlying sheaves of sets is unchanged by the transport along an equality of
restriction morphisms. -/
lemma derivationSheafHom_restrictScalarsDerivationCongr
    (M : SheafOfModules.{w} R) {u u' : (Stacks.forgetCommRingSheaf.{v, u, w} J).obj P ⟶ R}
    (h : u = u') {S : Sheaf J CommRingCat.{w}} (b : S ⟶ P)
    (DD : PresheafOfModulesOfCommRing.Derivation' ((SheafOfModules.restrictScalars u).obj M).val
      b.hom) :
    derivationSheafHom b ((SheafOfModules.restrictScalars u').obj M)
        (restrictScalarsDerivationCongr M h b DD) =
      derivationSheafHom b ((SheafOfModules.restrictScalars u).obj M) DD := by
  subst h
  rfl

variable {A' P' B' : Sheaf J CommRingCat.{w}}

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- Transport along an isomorphism of the acting sheaf of commutative rings commutes with
postcomposition by a morphism of the coefficient module. -/
lemma derivationRingEquiv_postcomp
    {M N : SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf.{u, v, w} B')} (k : M ⟶ N)
    (rho : P ≅ P') {baseP : A' ⟶ P} {baseP' : A' ⟶ P'} {augP : P ⟶ B'} {augP' : P' ⟶ B'}
    (hbase : baseP ≫ rho.hom = baseP') (haug : rho.hom ≫ augP' = augP)
    (DD : PresheafOfModulesOfCommRing.Derivation' ((SheafOfModules.restrictScalars
        ((Stacks.forgetCommRingSheaf.{v, u, w} J).map augP)).obj M).val baseP.hom) :
    derivationRingEquiv N rho hbase haug (DD.postcomp
        ((SheafOfModules.restrictScalars
          ((Stacks.forgetCommRingSheaf.{v, u, w} J).map augP)).map k).val) =
      (derivationRingEquiv M rho hbase haug DD).postcomp
        ((SheafOfModules.restrictScalars
          ((Stacks.forgetCommRingSheaf.{v, u, w} J).map augP')).map k).val := rfl

end RestrictCongr

/-! ## Naturality of the hom-set bijection of `f⁻¹ ⊣ f_*` in the source -/

section HomEquivLeft

universe w w' v u v' u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  (O : Sheaf K RingCat.{w'})

/-- The hom-set bijection of `f⁻¹ ⊣ f_*` for sheaves of modules is natural in the source. -/
lemma toposModulesHomEquiv_naturality_left {G G' : SheafOfModules.{w'} O}
    (p : G ⟶ G') {F : SheafOfModules.{w} (inverseImageRingSheaf f O)}
    (α : (inverseImageModules f O).obj G' ⟶ F) :
    toposModulesHomEquiv f O G F ((inverseImageModules f O).map p ≫ α) =
      p ≫ toposModulesHomEquiv f O G' F α := by
  refine hom_ext_moduleSheafFunctor ?_
  rw [moduleSheafFunctor_map_toposModulesHomEquiv, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp, moduleSheafFunctor_map_toposModulesHomEquiv,
    moduleSheafFunctor_map_inverseImageModules_map]
  exact f.adj.homEquiv_naturality_left _ _

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})] in
/-- The morphism of underlying sheaves of sets of the inverse image of a morphism of sheaves of
commutative rings is the inverse image of its morphism of underlying sheaves of sets. -/
lemma commRingSetHom_inverseImageRing_map {O O' : Sheaf K CommRingCat.{w'}} (q : O ⟶ O') :
    commRingSetHom.{w, v, u} (f.inverseImageRing.map q) =
      f.inverseImage.map (commRingSetHom.{w', v', u'} q) :=
  (congrArg (sheafCompose J (forget RingCat.{w})).map
      (forgetCommRingSheaf_map_pullbackCommRingSheafMap J f.inverseImage q)).trans
    (ringSheafMap_pullbackRingSheafMap J f.inverseImage
      ((Stacks.forgetCommRingSheaf.{v', u', w'} K).map q))

end HomEquivLeft

end Stacks.Sheaves.RingedToposModules

namespace CategoryTheory.Sheaf

universe u v w u' v' w'

open Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (f : MorphismOfTopoi (Sheaf J (Type (max u v w))) (Sheaf K (Type (max u' v' w'))))
  {A B : Sheaf K CommRingCat.{max u' v' w'}} (a : A ⟶ B)

/-! ## The corepresentation -/

/-- The inverse image of the base-changed simplicial module `Ω_{P_•/A} ⊗_{P_•} B` of `a`. -/
noncomputable abbrev inverseImageCotangentObject :
    SimplicialObject (targetModules.{u, v, w} J (f.inverseImageRing.obj B)) :=
  (cotangentSimplicialModule.{u', v', w'} K a).object ⋙
    inverseImageTargetModules.{u, v, w, u', v', w'} J K f

/-- A sheaf of `f⁻¹B`-modules, read as a sheaf of modules over the inverse image of the
degree-`n` term of the standard resolution of `a`. -/
noncomputable abbrev inverseImageRestrictedModule (n : SimplexCategoryᵒᵖ)
    (M : targetModules.{u, v, w} J (f.inverseImageRing.obj B)) :
    SheafOfModules.{max u v w}
      ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (J := J))
        (f.inverseImageRing.obj (resolutionTerm.{u', v', w'} K a n))) :=
  (SheafOfModules.restrictScalars
    (inverseImageRingMap f (resolutionAugmentationRing.{u', v', w'} K a n))).obj M

/-- The inverse image of the underlying morphism of sheaves of rings of the augmentation is the
underlying morphism of sheaves of rings of its inverse image. -/
lemma inverseImageRingMap_resolutionAugmentationRing (n : SimplexCategoryᵒᵖ) :
    inverseImageRingMap f (resolutionAugmentationRing.{u', v', w'} K a n) =
      (Stacks.forgetCommRingSheaf.{v, u, max u v w} J).map
        (f.inverseImageRing.map (resolutionAugmentation.{u', v', w'} K a n)) :=
  (forgetCommRingSheaf_map_pullbackCommRingSheafMap J f.inverseImage
    (resolutionAugmentation.{u', v', w'} K a n)).symm

/-- The direct image of a sheaf of `f⁻¹B`-modules, read over the degree-`n` term of the standard
resolution of `a` through the augmentation, is the direct image of that sheaf read over the
inverse image of that term. -/
noncomputable abbrev directImageRestrictedIso (n : SimplexCategoryᵒᵖ)
    (M : targetModules.{u, v, w} J (f.inverseImageRing.obj B)) :
    (SheafOfModules.restrictScalars (resolutionAugmentationRing.{u', v', w'} K a n)).obj
        ((directImageModules f
            ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) B)).obj M) ≅
      (directImageModules f
          ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K))
            (resolutionTerm.{u', v', w'} K a n))).obj
        (inverseImageRestrictedModule.{u, v, w, u', v', w'} J K f a n M) :=
  directImageModulesRestrictScalarsIso f (resolutionAugmentationRing.{u', v', w'} K a n) M

/-- The `A`-derivation of the degree-`n` term of the standard resolution of `a`, with values in
the direct image of `M`, attached to a morphism out of the inverse image of
`Ω_{P_n/A} ⊗_{P_n} B`. -/
noncomputable def pushforwardCotangentDerivation (n : SimplexCategoryᵒᵖ)
    (M : targetModules.{u, v, w} J (f.inverseImageRing.obj B))
    (g : (inverseImageCotangentObject.{u, v, w, u', v', w'} J K f a).obj n ⟶ M) :
    resolutionDerivations.{u', v', w'} K a n
      ((directImageModules f
          ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) B)).obj M) :=
  (cotangentSimplicialModule.{u', v', w'} K a).derivationEquiv n _
    (toposModulesHomEquiv f
      ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) B)
      ((cotangentSimplicialModule.{u', v', w'} K a).object.obj n) M g)

/-- **The inverse image of `Ω_{P_•/A} ⊗_{P_•} B` corepresents the derivations of the standard
resolution of `f⁻¹a`.** A morphism out of its degree-`n` term is, by the hom-set bijection of
Stacks 03D3, a morphism into the direct image, hence an `A`-derivation of `P_n`, hence by
transposition an `f⁻¹A`-derivation of `f⁻¹P_n`, hence by the degreewise comparison of the
standard resolutions an `f⁻¹A`-derivation of the degree-`n` term of the standard resolution
of `f⁻¹a`. -/
noncomputable def inverseImageCotangentDerivationEquiv (n : SimplexCategoryᵒᵖ)
    (M : targetModules.{u, v, w} J (f.inverseImageRing.obj B)) :
    ((inverseImageCotangentObject.{u, v, w, u', v', w'} J K f a).obj n ⟶ M) ≃
      resolutionDerivations.{u, v, w} J (f.inverseImageRing.map a) n M :=
  (toposModulesHomEquiv f
    ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) B)
      ((cotangentSimplicialModule.{u', v', w'} K a).object.obj n) M).trans
    (((cotangentSimplicialModule.{u', v', w'} K a).derivationEquiv n
        ((directImageModules f
          ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K))
            B)).obj M)).trans
      ((PresheafOfModules.Derivation.postcompEquiv
          ((SheafOfModules.forget _).mapIso
            (directImageRestrictedIso.{u, v, w, u', v', w'} J K f a n M))).trans
        (((inverseImageDerivationEquiv f (resolutionBase.{u', v', w'} K a n)
              (inverseImageRestrictedModule.{u, v, w, u', v', w'} J K f a n M)).symm).trans
          ((restrictScalarsDerivationCongr M
              (inverseImageRingMap_resolutionAugmentationRing.{u, v, w, u', v', w'} J K f a n)
              (f.inverseImageRing.map (resolutionBase.{u', v', w'} K a n))).trans
            (derivationRingEquiv M
              (resolutionInverseImageIso.{u, v, w, u', v', w'} J K f a n)
              (resolutionInverseImageIso_base.{u, v, w, u', v', w'} J K f a n)
              (resolutionInverseImageIso_augmentation.{u, v, w, u', v', w'} J K f a n))))))

/-- The corepresented derivation, written out through the five transports. -/
lemma inverseImageCotangentDerivationEquiv_apply (n : SimplexCategoryᵒᵖ)
    (M : targetModules.{u, v, w} J (f.inverseImageRing.obj B))
    (g : (inverseImageCotangentObject.{u, v, w, u', v', w'} J K f a).obj n ⟶ M) :
    inverseImageCotangentDerivationEquiv.{u, v, w, u', v', w'} J K f a n M g =
      derivationRingEquiv M
        (resolutionInverseImageIso.{u, v, w, u', v', w'} J K f a n)
        (resolutionInverseImageIso_base.{u, v, w, u', v', w'} J K f a n)
        (resolutionInverseImageIso_augmentation.{u, v, w, u', v', w'} J K f a n)
        (restrictScalarsDerivationCongr M
          (inverseImageRingMap_resolutionAugmentationRing.{u, v, w, u', v', w'} J K f a n)
          (f.inverseImageRing.map (resolutionBase.{u', v', w'} K a n))
          ((inverseImageDerivationEquiv f (resolutionBase.{u', v', w'} K a n)
              (inverseImageRestrictedModule.{u, v, w, u', v', w'} J K f a n M)).symm
            ((pushforwardCotangentDerivation.{u, v, w, u', v', w'} J K f a n M g).postcomp
              (directImageRestrictedIso.{u, v, w, u', v', w'} J K f a n M).hom.val))) :=
  rfl

/-- **The morphism of underlying sheaves of sets of the corepresented derivation.** The three
transports act on it by composition: the comparison of the standard resolutions on the source,
the identification of the direct image with the restriction of scalars on the target, and the
transposition by the hom-set bijection of `f⁻¹ ⊣ f_*`. -/
lemma derivationSheafHom_inverseImageCotangentDerivationEquiv (n : SimplexCategoryᵒᵖ)
    (M : targetModules.{u, v, w} J (f.inverseImageRing.obj B))
    (g : (inverseImageCotangentObject.{u, v, w, u', v', w'} J K f a).obj n ⟶ M) :
    derivationSheafHom (resolutionBase.{u, v, w} J (f.inverseImageRing.map a) n)
        ((SheafOfModules.restrictScalars
          (resolutionAugmentationRing.{u, v, w} J (f.inverseImageRing.map a) n)).obj M)
        (inverseImageCotangentDerivationEquiv.{u, v, w, u', v', w'} J K f a n M g) =
      commRingSetHom (resolutionInverseImageIso.{u, v, w, u', v', w'} J K f a n).inv ≫
        (f.adj.homEquiv _ _).symm
          (derivationSheafHom (resolutionBase.{u', v', w'} K a n)
              ((SheafOfModules.restrictScalars
                  (resolutionAugmentationRing.{u', v', w'} K a n)).obj
                ((directImageModules f
                    ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K))
                      B)).obj M))
              (pushforwardCotangentDerivation.{u, v, w, u', v', w'} J K f a n M g) ≫
            eqToHom (moduleSheaf_directImageModules_restrictScalars f
              (resolutionAugmentationRing.{u', v', w'} K a n) M)) := by
  refine (derivationSheafHom_derivationRingEquiv M
      (resolutionInverseImageIso.{u, v, w, u', v', w'} J K f a n)
      (resolutionInverseImageIso_base.{u, v, w, u', v', w'} J K f a n)
      (resolutionInverseImageIso_augmentation.{u, v, w, u', v', w'} J K f a n) _).trans ?_
  refine congrArg (fun m ↦
    commRingSetHom (resolutionInverseImageIso.{u, v, w, u', v', w'} J K f a n).inv ≫ m) ?_
  refine (derivationSheafHom_restrictScalarsDerivationCongr
      (P := f.inverseImageRing.obj (resolutionTerm.{u', v', w'} K a n))
      (u := inverseImageRingMap f (resolutionAugmentationRing.{u', v', w'} K a n)) M
      (inverseImageRingMap_resolutionAugmentationRing.{u, v, w, u', v', w'} J K f a n)
      (f.inverseImageRing.map (resolutionBase.{u', v', w'} K a n)) _).trans ?_
  refine ((f.adj.homEquiv _ _).eq_symm_apply).mpr ?_
  refine (derivationSheafHom_inverseImageDerivationEquiv f
      (resolutionBase.{u', v', w'} K a n)
      (inverseImageRestrictedModule.{u, v, w, u', v', w'} J K f a n M) _).symm.trans ?_
  refine (congrArg (fun DD ↦ derivationSheafHom (resolutionBase.{u', v', w'} K a n)
      ((directImageModules f
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K))
          (resolutionTerm.{u', v', w'} K a n))).obj
        (inverseImageRestrictedModule.{u, v, w, u', v', w'} J K f a n M)) DD)
    ((inverseImageDerivationEquiv f (resolutionBase.{u', v', w'} K a n)
      (inverseImageRestrictedModule.{u, v, w, u', v', w'}
        J K f a n M)).apply_symm_apply _)).trans ?_
  exact (derivationSheafHom_postcomp (resolutionBase.{u', v', w'} K a n)
      (directImageRestrictedIso.{u, v, w, u', v', w'} J K f a n M).hom
      (pushforwardCotangentDerivation.{u, v, w, u', v', w'} J K f a n M g)).trans
    (congrArg (fun m ↦ derivationSheafHom (resolutionBase.{u', v', w'} K a n)
        ((SheafOfModules.restrictScalars
            (resolutionAugmentationRing.{u', v', w'} K a n)).obj
          ((directImageModules f
            ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) B)).obj M))
        (pushforwardCotangentDerivation.{u, v, w, u', v', w'} J K f a n M g) ≫ m)
      (moduleSheafFunctor_map_directImageModulesRestrictScalarsIso_hom f
        (resolutionAugmentationRing.{u', v', w'} K a n) M))

/-- The derivation of `P_n` attached to a morphism is natural in the coefficient module. -/
lemma pushforwardCotangentDerivation_naturality (n : SimplexCategoryᵒᵖ)
    {M N : targetModules.{u, v, w} J (f.inverseImageRing.obj B)}
    (g : (inverseImageCotangentObject.{u, v, w, u', v', w'} J K f a).obj n ⟶ M) (h : M ⟶ N) :
    pushforwardCotangentDerivation.{u, v, w, u', v', w'} J K f a n N (g ≫ h) =
      (pushforwardCotangentDerivation.{u, v, w, u', v', w'} J K f a n M g).postcomp
        ((SheafOfModules.restrictScalars (resolutionAugmentationRing.{u', v', w'} K a n)).map
          ((directImageModules f
              ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K))
                B)).map h)).val :=
  (congrArg ((cotangentSimplicialModule.{u', v', w'} K a).derivationEquiv n
        ((directImageModules f
          ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) B)).obj N))
      (toposModulesHomEquiv_naturality_right f
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) B)
        ((cotangentSimplicialModule.{u', v', w'} K a).object.obj n) g h)).trans
    ((cotangentSimplicialModule.{u', v', w'} K a).naturality n
      (toposModulesHomEquiv f
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) B)
        ((cotangentSimplicialModule.{u', v', w'} K a).object.obj n) M g)
      ((directImageModules f
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) B)).map h))

/-- **The corepresentation is natural in the coefficient module.** -/
lemma inverseImageCotangentDerivationEquiv_naturality (n : SimplexCategoryᵒᵖ)
    {M N : targetModules.{u, v, w} J (f.inverseImageRing.obj B)}
    (g : (inverseImageCotangentObject.{u, v, w, u', v', w'} J K f a).obj n ⟶ M) (h : M ⟶ N) :
    inverseImageCotangentDerivationEquiv.{u, v, w, u', v', w'} J K f a n N (g ≫ h) =
      (inverseImageCotangentDerivationEquiv.{u, v, w, u', v', w'} J K f a n M g).postcomp
        ((SheafOfModules.restrictScalars
          (resolutionAugmentationRing.{u, v, w} J (f.inverseImageRing.map a) n)).map h).val := by
  have hq : ((pushforwardCotangentDerivation.{u, v, w, u', v', w'} J K f a n N (g ≫ h)).postcomp
        (directImageRestrictedIso.{u, v, w, u', v', w'} J K f a n N).hom.val) =
      ((pushforwardCotangentDerivation.{u, v, w, u', v', w'} J K f a n M g).postcomp
          (directImageRestrictedIso.{u, v, w, u', v', w'} J K f a n M).hom.val).postcomp
        ((directImageModules f
          ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K))
            (resolutionTerm.{u', v', w'} K a n))).map
          ((SheafOfModules.restrictScalars
            (inverseImageRingMap f (resolutionAugmentationRing.{u', v', w'} K a n))).map h)).val :=
    (congrArg (fun DD ↦ PresheafOfModulesOfCommRing.Derivation.postcomp DD
          (directImageRestrictedIso.{u, v, w, u', v', w'} J K f a n N).hom.val)
        (pushforwardCotangentDerivation_naturality.{u, v, w, u', v', w'} J K f a n g h)).trans
      ((PresheafOfModules.Derivation.postcomp_postcomp _ _ _).trans
        ((congrArg (fun m ↦ PresheafOfModulesOfCommRing.Derivation.postcomp
              (pushforwardCotangentDerivation.{u, v, w, u', v', w'} J K f a n M g)
              (SheafOfModules.Hom.val m))
            ((directImageModulesCompRestrictScalarsIso f
              (resolutionAugmentationRing.{u', v', w'} K a n)).hom.naturality h)).trans
          (PresheafOfModules.Derivation.postcomp_postcomp _ _ _).symm))
  have hs := inverseImageDerivationEquiv_symm_postcomp f (resolutionBase.{u', v', w'} K a n)
    ((SheafOfModules.restrictScalars
      (inverseImageRingMap f (resolutionAugmentationRing.{u', v', w'} K a n))).map h)
    ((pushforwardCotangentDerivation.{u, v, w, u', v', w'} J K f a n M g).postcomp
      (directImageRestrictedIso.{u, v, w, u', v', w'} J K f a n M).hom.val)
  rw [inverseImageCotangentDerivationEquiv_apply, inverseImageCotangentDerivationEquiv_apply, hq,
    ← hs]
  refine (congrArg _ (restrictScalarsDerivationCongr_postcomp h
    (inverseImageRingMap_resolutionAugmentationRing.{u, v, w, u', v', w'} J K f a n) _ _)).trans ?_
  exact derivationRingEquiv_postcomp h _ _ _ _

/-! ## Compatibility with the simplex maps -/

/-- The transpose of the morphism of underlying sheaves of sets of the `A`-derivation of `P_n`:
the corepresented derivation, before the comparison of the standard resolutions. -/
noncomputable def transposedCotangentSheafHom (n : SimplexCategoryᵒᵖ)
    (M : targetModules.{u, v, w} J (f.inverseImageRing.obj B))
    (g : (inverseImageCotangentObject.{u, v, w, u', v', w'} J K f a).obj n ⟶ M) :
    f.inverseImage.obj (Sheaf.ringSheaf.{max u' v' w', v', u'}
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K))
          (resolutionTerm.{u', v', w'} K a n))) ⟶
      Sheaf.moduleSheaf.{max u v w, v, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (J := J))
          (f.inverseImageRing.obj (resolutionTerm.{u', v', w'} K a n)))
        (inverseImageRestrictedModule.{u, v, w, u', v', w'} J K f a n M) :=
  (f.adj.homEquiv
      (Sheaf.ringSheaf.{max u' v' w', v', u'}
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K))
          (resolutionTerm.{u', v', w'} K a n)))
      (Sheaf.moduleSheaf.{max u v w, v, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (J := J))
          (f.inverseImageRing.obj (resolutionTerm.{u', v', w'} K a n)))
        (inverseImageRestrictedModule.{u, v, w, u', v', w'} J K f a n M))).symm
    (derivationSheafHom (resolutionBase.{u', v', w'} K a n)
        ((SheafOfModules.restrictScalars (resolutionAugmentationRing.{u', v', w'} K a n)).obj
          ((directImageModules f
            ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) B)).obj M))
        (pushforwardCotangentDerivation.{u, v, w, u', v', w'} J K f a n M g) ≫
      eqToHom (moduleSheaf_directImageModules_restrictScalars f
        (resolutionAugmentationRing.{u', v', w'} K a n) M))

/-- The morphism of underlying sheaves of sets of the corepresented derivation, written through
`CategoryTheory.Sheaf.transposedCotangentSheafHom`. -/
lemma derivationSheafHom_inverseImageCotangentDerivationEquiv' (n : SimplexCategoryᵒᵖ)
    (M : targetModules.{u, v, w} J (f.inverseImageRing.obj B))
    (g : (inverseImageCotangentObject.{u, v, w, u', v', w'} J K f a).obj n ⟶ M) :
    derivationSheafHom (resolutionBase.{u, v, w} J (f.inverseImageRing.map a) n)
        ((SheafOfModules.restrictScalars
          (resolutionAugmentationRing.{u, v, w} J (f.inverseImageRing.map a) n)).obj M)
        (inverseImageCotangentDerivationEquiv.{u, v, w, u', v', w'} J K f a n M g) =
      commRingSetHom.{max u v w, v, u}
          (resolutionInverseImageIso.{u, v, w, u', v', w'} J K f a n).inv ≫
        transposedCotangentSheafHom.{u, v, w, u', v', w'} J K f a n M g :=
  derivationSheafHom_inverseImageCotangentDerivationEquiv.{u, v, w, u', v', w'} J K f a n M g

/-- The degreewise comparison of the standard resolutions is natural in the simplex. -/
lemma resolutionInverseImageIso_naturality {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j) :
    f.inverseImageRing.map (((standardResolution.{v', u', w'} K a).left.map g).right) ≫
        (resolutionInverseImageIso.{u, v, w, u', v', w'} J K f a j).hom =
      (resolutionInverseImageIso.{u, v, w, u', v', w'} J K f a i).hom ≫
        ((standardResolution.{v, u, w} J (f.inverseImageRing.map a)).left.map g).right :=
  congrArg (fun ψ ↦ Under.Hom.right ψ)
    ((standardResolutionInverseImageIso.{u, v, w, u', v', w'} J K f a).hom.naturality g)

/-- The inverse of the degreewise comparison is natural in the simplex. -/
lemma resolutionInverseImageIso_inv_naturality {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j) :
    (resolutionInverseImageIso.{u, v, w, u', v', w'} J K f a i).inv ≫
        f.inverseImageRing.map (((standardResolution.{v', u', w'} K a).left.map g).right) =
      ((standardResolution.{v, u, w} J (f.inverseImageRing.map a)).left.map g).right ≫
        (resolutionInverseImageIso.{u, v, w, u', v', w'} J K f a j).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc,
    ← resolutionInverseImageIso_naturality.{u, v, w, u', v', w'} J K f a g, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- The derivation of `P_i` attached to a morphism out of the degree-`j` term, read on sections:
it is the derivation of `P_j` evaluated at the image of the section. -/
lemma pushforwardCotangentDerivation_simplex {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j)
    (M : targetModules.{u, v, w} J (f.inverseImageRing.obj B))
    (h : (inverseImageCotangentObject.{u, v, w, u', v', w'} J K f a).obj j ⟶ M) (Y : Dᵒᵖ)
    (y : (resolutionTerm.{u', v', w'} K a i).obj.obj Y) :
    (pushforwardCotangentDerivation.{u, v, w, u', v', w'} J K f a i M
        ((inverseImageCotangentObject.{u, v, w, u', v', w'} J K f a).map g ≫ h)).d y =
      (pushforwardCotangentDerivation.{u, v, w, u', v', w'} J K f a j M h).d
        ((((standardResolution.{v', u', w'} K a).left.map g).right.hom.app Y) y) :=
  (PresheafOfModulesOfCommRing.Derivation.congr_d (X := Y)
      (congrArg ((cotangentSimplicialModule.{u', v', w'} K a).derivationEquiv i
          ((directImageModules f
            ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) B)).obj M))
        (toposModulesHomEquiv_naturality_left f
          ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) B)
          ((cotangentSimplicialModule.{u', v', w'} K a).object.map g) h)) y).trans
    ((cotangentSimplicialModule.{u', v', w'} K a).simplex_naturality g
      ((directImageModules f
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) B)).obj M)
      (toposModulesHomEquiv f
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) B)
        ((cotangentSimplicialModule.{u', v', w'} K a).object.obj j) M h) Y y)

/-- The K-side comparison of the two simplicial degrees, as an equality of morphisms of the
underlying sheaves of sets. -/
lemma derivationSheafHom_pushforwardCotangentDerivation_simplex {i j : SimplexCategoryᵒᵖ}
    (g : i ⟶ j) (M : targetModules.{u, v, w} J (f.inverseImageRing.obj B))
    (h : (inverseImageCotangentObject.{u, v, w, u', v', w'} J K f a).obj j ⟶ M) :
    derivationSheafHom (resolutionBase.{u', v', w'} K a i)
        ((SheafOfModules.restrictScalars (resolutionAugmentationRing.{u', v', w'} K a i)).obj
          ((directImageModules f
              ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) B)).obj M))
        (pushforwardCotangentDerivation.{u, v, w, u', v', w'} J K f a i M
          ((inverseImageCotangentObject.{u, v, w, u', v', w'} J K f a).map g ≫ h)) =
      commRingSetHom.{max u' v' w', v', u'}
          (((standardResolution.{v', u', w'} K a).left.map g).right) ≫
        derivationSheafHom (resolutionBase.{u', v', w'} K a j)
          ((SheafOfModules.restrictScalars (resolutionAugmentationRing.{u', v', w'} K a j)).obj
            ((directImageModules f
                ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K))
                  B)).obj M))
          (pushforwardCotangentDerivation.{u, v, w, u', v', w'} J K f a j M h) :=
  Sheaf.hom_ext_sections fun Y y ↦
    pushforwardCotangentDerivation_simplex.{u, v, w, u', v', w'} J K f a g M h Y y

/-- The two simplicial degrees give the same identification of underlying sheaves of sets: both
identify the direct image of a restriction of scalars with the restriction of scalars of the
direct image, and the two identifications have the same type. -/
lemma eqToHom_moduleSheaf_directImageModules_restrictScalars_congr (i j : SimplexCategoryᵒᵖ)
    (M : targetModules.{u, v, w} J (f.inverseImageRing.obj B)) :
    eqToHom (moduleSheaf_directImageModules_restrictScalars f
        (resolutionAugmentationRing.{u', v', w'} K a i) M) =
      eqToHom (moduleSheaf_directImageModules_restrictScalars f
        (resolutionAugmentationRing.{u', v', w'} K a j) M) :=
  rfl

/-- The K-side comparison of the two simplicial degrees, after the identification of the direct
image with the restriction of scalars. -/
lemma pushforwardCotangentSheafHom_simplex {i j : SimplexCategoryᵒᵖ}
    (g : i ⟶ j) (M : targetModules.{u, v, w} J (f.inverseImageRing.obj B))
    (h : (inverseImageCotangentObject.{u, v, w, u', v', w'} J K f a).obj j ⟶ M) :
    derivationSheafHom (resolutionBase.{u', v', w'} K a i)
          ((SheafOfModules.restrictScalars (resolutionAugmentationRing.{u', v', w'} K a i)).obj
            ((directImageModules f
                ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K))
                  B)).obj M))
          (pushforwardCotangentDerivation.{u, v, w, u', v', w'} J K f a i M
            ((inverseImageCotangentObject.{u, v, w, u', v', w'} J K f a).map g ≫ h)) ≫
        eqToHom (moduleSheaf_directImageModules_restrictScalars f
          (resolutionAugmentationRing.{u', v', w'} K a i) M) =
      commRingSetHom.{max u' v' w', v', u'}
          (((standardResolution.{v', u', w'} K a).left.map g).right) ≫
        (derivationSheafHom (resolutionBase.{u', v', w'} K a j)
            ((SheafOfModules.restrictScalars (resolutionAugmentationRing.{u', v', w'} K a j)).obj
              ((directImageModules f
                  ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K))
                    B)).obj M))
            (pushforwardCotangentDerivation.{u, v, w, u', v', w'} J K f a j M h) ≫
          eqToHom (moduleSheaf_directImageModules_restrictScalars f
            (resolutionAugmentationRing.{u', v', w'} K a j) M)) := by
  rw [derivationSheafHom_pushforwardCotangentDerivation_simplex.{u, v, w, u', v', w'} J K f a g M h,
    eqToHom_moduleSheaf_directImageModules_restrictScalars_congr.{u, v, w, u', v', w'}
      J K f a i j M]
  exact Category.assoc _ _ _

/-- The inverse of the degreewise comparison, read on underlying sheaves of sets, intertwines the
two simplex maps. -/
lemma commRingSetHom_resolutionInverseImageIso_inv_simplex {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j) :
    commRingSetHom.{max u v w, v, u}
        (resolutionInverseImageIso.{u, v, w, u', v', w'} J K f a i).inv ≫
        f.inverseImage.map (commRingSetHom.{max u' v' w', v', u'}
          (((standardResolution.{v', u', w'} K a).left.map g).right)) =
      commRingSetHom.{max u v w, v, u}
          (((standardResolution.{v, u, w} J (f.inverseImageRing.map a)).left.map g).right) ≫
        commRingSetHom.{max u v w, v, u}
          (resolutionInverseImageIso.{u, v, w, u', v', w'} J K f a j).inv :=
  (congrArg (fun m ↦ commRingSetHom.{max u v w, v, u}
        (resolutionInverseImageIso.{u, v, w, u', v', w'} J K f a i).inv ≫ m)
      (commRingSetHom_inverseImageRing_map f
        (((standardResolution.{v', u', w'} K a).left.map g).right)).symm).trans
    (((commRingSetHom_comp.{max u v w, v, u}
            (resolutionInverseImageIso.{u, v, w, u', v', w'} J K f a i).inv
            (f.inverseImageRing.map
              (((standardResolution.{v', u', w'} K a).left.map g).right))).symm.trans
        (congrArg (fun m ↦ commRingSetHom.{max u v w, v, u} m)
          (resolutionInverseImageIso_inv_naturality.{u, v, w, u', v', w'} J K f a g))).trans
      (commRingSetHom_comp.{max u v w, v, u}
        (((standardResolution.{v, u, w} J (f.inverseImageRing.map a)).left.map g).right)
        (resolutionInverseImageIso.{u, v, w, u', v', w'} J K f a j).inv))

/-- The transposed morphism of underlying sheaves of sets intertwines the two simplex maps. -/
lemma transposedCotangentSheafHom_simplex {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j)
    (M : targetModules.{u, v, w} J (f.inverseImageRing.obj B))
    (h : (inverseImageCotangentObject.{u, v, w, u', v', w'} J K f a).obj j ⟶ M) :
    transposedCotangentSheafHom.{u, v, w, u', v', w'} J K f a i M
        ((inverseImageCotangentObject.{u, v, w, u', v', w'} J K f a).map g ≫ h) =
      f.inverseImage.map (commRingSetHom.{max u' v' w', v', u'}
          (((standardResolution.{v', u', w'} K a).left.map g).right)) ≫
        transposedCotangentSheafHom.{u, v, w, u', v', w'} J K f a j M h :=
  (congrArg (fun m ↦ (f.adj.homEquiv
        (Sheaf.ringSheaf.{max u' v' w', v', u'}
          ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K))
            (resolutionTerm.{u', v', w'} K a i)))
        (Sheaf.moduleSheaf.{max u v w, v, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (J := J))
            (f.inverseImageRing.obj (resolutionTerm.{u', v', w'} K a i)))
          (inverseImageRestrictedModule.{u, v, w, u', v', w'} J K f a i M))).symm m)
      (pushforwardCotangentSheafHom_simplex.{u, v, w, u', v', w'} J K f a g M h)).trans
    (f.adj.homEquiv_naturality_left_symm
      (Y := Sheaf.moduleSheaf.{max u v w, v, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (J := J))
          (f.inverseImageRing.obj (resolutionTerm.{u', v', w'} K a i)))
        (inverseImageRestrictedModule.{u, v, w, u', v', w'} J K f a i M))
      (commRingSetHom.{max u' v' w', v', u'}
        (((standardResolution.{v', u', w'} K a).left.map g).right)) _)

/-- **The corepresentation is compatible with the simplex maps**, as an equality of the morphisms
of underlying sheaves of sets. -/
lemma derivationSheafHom_inverseImageCotangentDerivationEquiv_simplex {i j : SimplexCategoryᵒᵖ}
    (g : i ⟶ j) (M : targetModules.{u, v, w} J (f.inverseImageRing.obj B))
    (h : (inverseImageCotangentObject.{u, v, w, u', v', w'} J K f a).obj j ⟶ M) :
    derivationSheafHom (resolutionBase.{u, v, w} J (f.inverseImageRing.map a) i)
        ((SheafOfModules.restrictScalars
          (resolutionAugmentationRing.{u, v, w} J (f.inverseImageRing.map a) i)).obj M)
        (inverseImageCotangentDerivationEquiv.{u, v, w, u', v', w'} J K f a i M
          ((inverseImageCotangentObject.{u, v, w, u', v', w'} J K f a).map g ≫ h)) =
      commRingSetHom.{max u v w, v, u}
          (((standardResolution.{v, u, w} J (f.inverseImageRing.map a)).left.map g).right) ≫
        derivationSheafHom (resolutionBase.{u, v, w} J (f.inverseImageRing.map a) j)
          ((SheafOfModules.restrictScalars
            (resolutionAugmentationRing.{u, v, w} J (f.inverseImageRing.map a) j)).obj M)
          (inverseImageCotangentDerivationEquiv.{u, v, w, u', v', w'} J K f a j M h) := by
  rw [derivationSheafHom_inverseImageCotangentDerivationEquiv',
    derivationSheafHom_inverseImageCotangentDerivationEquiv',
    transposedCotangentSheafHom_simplex.{u, v, w, u', v', w'} J K f a g M h]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m ↦ m ≫ transposedCotangentSheafHom.{u, v, w, u', v', w'} J K f a j M h)
      (commRingSetHom_resolutionInverseImageIso_inv_simplex.{u, v, w, u', v', w'}
        J K f a g)).trans (Category.assoc _ _ _))

/-- **The corepresentation is compatible with the simplex maps**, read on sections. -/
lemma inverseImageCotangentDerivationEquiv_simplex_naturality {i j : SimplexCategoryᵒᵖ}
    (g : i ⟶ j) (M : targetModules.{u, v, w} J (f.inverseImageRing.obj B))
    (h : (inverseImageCotangentObject.{u, v, w, u', v', w'} J K f a).obj j ⟶ M) (U : Cᵒᵖ)
    (x : (Sheaf.sectionsFunctor.{max u v w} J U).obj
      (Sheaf.ringSheaf.{max u v w, v, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (J := J))
          (resolutionTerm.{u, v, w} J (f.inverseImageRing.map a) i)))) :
    (Sheaf.sectionsFunctor.{max u v w} J U).map
        (derivationSheafHom (resolutionBase.{u, v, w} J (f.inverseImageRing.map a) i)
          ((SheafOfModules.restrictScalars
            (resolutionAugmentationRing.{u, v, w} J (f.inverseImageRing.map a) i)).obj M)
          (inverseImageCotangentDerivationEquiv.{u, v, w, u', v', w'} J K f a i M
            ((inverseImageCotangentObject.{u, v, w, u', v', w'} J K f a).map g ≫ h))) x =
      (Sheaf.sectionsFunctor.{max u v w} J U).map
          (derivationSheafHom (resolutionBase.{u, v, w} J (f.inverseImageRing.map a) j)
            ((SheafOfModules.restrictScalars
              (resolutionAugmentationRing.{u, v, w} J (f.inverseImageRing.map a) j)).obj M)
            (inverseImageCotangentDerivationEquiv.{u, v, w, u', v', w'} J K f a j M h))
        ((Sheaf.sectionsFunctor.{max u v w} J U).map
          (commRingSetHom.{max u v w, v, u}
            (((standardResolution.{v, u, w} J (f.inverseImageRing.map a)).left.map g).right)) x) :=
  (congrArg (fun m ↦ (Sheaf.sectionsFunctor.{max u v w} J U).map m x)
      (derivationSheafHom_inverseImageCotangentDerivationEquiv_simplex.{u, v, w, u', v', w'}
        J K f a g M h)).trans
    ((Sheaf.sectionsFunctor.{max u v w} J U).map_comp_apply _ _ x)

/-! ## The inverse image of the cotangent complex -/

/-- **Stacks 08SV.** The inverse image of the base-changed simplicial module
`Ω_{P_•/A} ⊗_{P_•} B` of `a` is a base-changed simplicial module for `f⁻¹a`: it corepresents the
`f⁻¹A`-derivations of the standard resolution of `f⁻¹a`, naturally in the coefficient module and
compatibly with the simplex maps. -/
noncomputable def inverseImageCotangentData :
    CotangentSimplicialModuleData.{u, v, w} J (f.inverseImageRing.map a) where
  object := inverseImageCotangentObject.{u, v, w, u', v', w'} J K f a
  derivationEquiv := inverseImageCotangentDerivationEquiv.{u, v, w, u', v', w'} J K f a
  naturality n :=
    inverseImageCotangentDerivationEquiv_naturality.{u, v, w, u', v', w'} J K f a n
  simplex_naturality g M h U x :=
    inverseImageCotangentDerivationEquiv_simplex_naturality.{u, v, w, u', v', w'}
      J K f a g M h U x

/-- **Stacks 08SV.** The inverse image of the cotangent complex of a homomorphism of sheaves of
commutative rings along a morphism of topoi is the cotangent complex of its inverse image:
`f⁻¹L_{B/A} = L_{f⁻¹B/f⁻¹A}`. -/
@[stacks 08SV "for an arbitrary morphism of topoi, with the object, arrow and section universes
of the two sites independent"]
noncomputable def inverseImageCotangentComplexIso :
    ((inverseImageTargetModules.{u, v, w, u', v', w'} J K f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (cotangentComplex.{u', v', w'} K a) ≅
      cotangentComplex.{u, v, w} J (f.inverseImageRing.map a) := by
  refine (HomologicalComplex.mapHomologicalComplexExtendIso
      (inverseImageTargetModules.{u, v, w, u', v', w'} J K f)
      ((AlgebraicTopology.alternatingFaceMapComplex
          (targetModules.{u', v', w'} K B)).obj
        (cotangentSimplicialModule.{u', v', w'} K a).object)
      (ComplexShape.embeddingUpIntLE 0)).symm ≪≫ ?_
  refine (((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor
      (targetModules.{u, v, w} J (f.inverseImageRing.obj B))).mapIso
    ((AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso
        (inverseImageTargetModules.{u, v, w, u', v', w'} J K f)).app
      (cotangentSimplicialModule.{u', v', w'} K a).object)) ≪≫ ?_
  exact (inverseImageCotangentData.{u, v, w, u', v', w'} J K f a).complexIsoCotangentComplex

end CategoryTheory.Sheaf

end
