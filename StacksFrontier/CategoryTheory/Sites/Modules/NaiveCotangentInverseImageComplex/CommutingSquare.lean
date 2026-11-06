module

public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentInverseImageComplex.DegreeComparisons

/-!
# The commuting square and the isomorphism of complexes of Stacks 08TZ

The conormal chain identity read on local sections of the kernel ideal, the computation of both
sides of the commuting square of the degree `-1` and degree `0` comparisons with the conormal
differentials, the square `Stacks.SheafOfModules.inverseImageNaiveCotangentSquare` itself, and
the resulting isomorphism of two-term complexes
`Stacks.SheafOfModules.inverseImageNaiveCotangentComplexIso`.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.Sheaves.RingedToposModules

section ConormalChainSectionValues

universe t v u

open CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget AddCommGrpCat.{t})] {R : Sheaf J RingCat.{t}}
  {M N : SheafOfModules.{t} R}

/-- The underlying morphism of sheaves of sets of a morphism of sheaves of modules acts on
local sections as that morphism does. -/
lemma sectionsFunctor_map_moduleSheafFunctor_map (α : M ⟶ N) (U : Cᵒᵖ)
    (s : (Sheaf.sectionsFunctor J U).obj ((Sheaf.moduleSheafFunctor R).obj M)) :
    (Sheaf.sectionsFunctor J U).map ((Sheaf.moduleSheafFunctor R).map α) s =
      α.val.app U s := rfl

/-- The underlying morphism of sheaves of sets of the inclusion of the kernel of a morphism of
sheaves of modules carries a local section of the kernel to its underlying local section. -/
lemma sectionsFunctor_map_moduleSheafFunctor_map_kerIota (g : M ⟶ N) (U : Cᵒᵖ)
    (s : (Sheaf.sectionsFunctor J U).obj
      ((Sheaf.moduleSheafFunctor R).obj (SheafOfModules.kerObj g))) :
    (Sheaf.sectionsFunctor J U).map
        ((Sheaf.moduleSheafFunctor R).map (SheafOfModules.kerIota g)) s = s.1 := rfl

end ConormalChainSectionValues

section ChainConsumers

universe w w' v u v' u'

open CategoryTheory AlgebraicGeometry.SheafOfModules
open Stacks.Sites.Conormal

attribute [local implicit_reducible] CategoryTheory.sheafCompose

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{max u' v' w'})]
  (f : MorphismOfTopoi (Sheaf J (Type (max u v w))) (Sheaf K (Type (max u' v' w'))))
  (A : Sheaf K CommRingCat.{max u' v' w'})
  {B : Sheaf K CommRingCat.{max u' v' w'}} (φ : A ⟶ B)
  (M : SheafOfModules.{max u v w}
    (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj B)))
  {R : Sheaf K CommRingCat.{max u' v' w'}} (b : R ⟶ A)

/-- **The hypothesis of the conormal chain identity, from its form before the exchange of the
direct image with restriction of scalars.** A morphism out of the kernel ideal whose underlying
morphism of sheaves of sets is the kernel inclusion followed by a derivation stays of that form
when the exchange isomorphism is composed onto it, the derivation being postcomposed with that
isomorphism. -/
lemma inverseImageIdealChain_hypothesis
    (p : idealSheaf.{max u' v' w', v', u'} K (presentationRingHom.{max u' v' w', v', u'} K φ) ⟶
      (SheafOfModules.restrictScalars (presentationRingHom.{max u' v' w', v', u'} K φ)).obj
        ((directImageCommModules.{w, w', v, u, v', u'} f B).obj M))
    (DD : PresheafOfModulesOfCommRing.Derivation' (((SheafOfModules.restrictScalars
          (presentationRingHom.{max u' v' w', v', u'} K φ)).obj
        ((directImageCommModules.{w, w', v, u, v', u'} f B).obj M)).val) b.hom)
    (hp0 : (Sheaf.moduleSheafFunctor
            (SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} A)).map p =
      (Sheaf.moduleSheafFunctor (SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} A)).map
          (SheafOfModules.kerIota (presentationModuleHom.{max u' v' w', v', u'} K
            (presentationRingHom.{max u' v' w', v', u'} K φ))) ≫
        derivationSheafHom b
          ((SheafOfModules.restrictScalars
            (presentationRingHom.{max u' v' w', v', u'} K φ)).obj
              ((directImageCommModules.{w, w', v, u, v', u'} f B).obj M)) DD) :
    (Sheaf.moduleSheafFunctor (SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} A)).map p ≫
          (Sheaf.moduleSheafFunctor (SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} A)).map
            (directImageRestrictScalarsIso f φ M).hom =
      (Sheaf.moduleSheafFunctor (SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} A)).map
          (SheafOfModules.kerIota (presentationModuleHom.{max u' v' w', v', u'} K
            (presentationRingHom.{max u' v' w', v', u'} K φ))) ≫
        derivationSheafHom b
          ((directImageCommModules.{w, w', v, u, v', u'} f A).obj
            ((SheafOfModules.restrictScalars
              (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).obj M))
          (DD.postcomp (directImageRestrictScalarsIso f φ M).hom.val) := by
  have h4 := congrArg (fun m ↦ m ≫ (Sheaf.moduleSheafFunctor
    (SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} A)).map
      (directImageRestrictScalarsIso f φ M).hom) hp0
  have hd := derivationSheafHom_postcomp b (directImageRestrictScalarsIso f φ M).hom DD
  have h5 := congrArg (fun m ↦ (Sheaf.moduleSheafFunctor
    (SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} A)).map
      (SheafOfModules.kerIota (presentationModuleHom.{max u' v' w', v', u'} K
        (presentationRingHom.{max u' v' w', v', u'} K φ))) ≫ m) hd.symm
  exact h4.trans ((Category.assoc _ _ _).trans h5)

/-- `Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_inverseImageIdealChain` read on a
local section of the kernel ideal of the inverse image: the transported morphism sends the
section to the value there of the transposed derivation. -/
lemma inverseImageIdealChain_app
    (p : idealSheaf.{max u' v' w', v', u'} K (presentationRingHom.{max u' v' w', v', u'} K φ) ⟶
      (SheafOfModules.restrictScalars (presentationRingHom.{max u' v' w', v', u'} K φ)).obj
        ((directImageCommModules.{w, w', v, u, v', u'} f B).obj M))
    (DD : PresheafOfModulesOfCommRing.Derivation' (((SheafOfModules.restrictScalars
          (presentationRingHom.{max u' v' w', v', u'} K φ)).obj
        ((directImageCommModules.{w, w', v, u, v', u'} f B).obj M)).val) b.hom)
    (hp : (Sheaf.moduleSheafFunctor
            (SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} A)).map p ≫
          (Sheaf.moduleSheafFunctor (SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} A)).map
            (directImageRestrictScalarsIso f φ M).hom =
      (Sheaf.moduleSheafFunctor (SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} A)).map
          (SheafOfModules.kerIota (presentationModuleHom.{max u' v' w', v', u'} K
            (presentationRingHom.{max u' v' w', v', u'} K φ))) ≫
        derivationSheafHom b
          ((directImageCommModules.{w, w', v, u, v', u'} f A).obj
            ((SheafOfModules.restrictScalars
              (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).obj M))
          (DD.postcomp (directImageRestrictScalarsIso f φ M).hom.val))
    (U : Cᵒᵖ)
    (g : ((idealSheaf.{max u v w, v, u} J
      (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).val.obj U)) :
    (inverseImageIdealTransportEquiv f φ M (inverseImageIdealAdjunctionEquiv f φ M
        (conormalIdealDirectImageRestrictEquiv f φ M p))).val.app U g =
      ((inverseImageDerivationEquiv f b ((SheafOfModules.restrictScalars
            (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).obj M)).symm
          (DD.postcomp (directImageRestrictScalarsIso f φ M).hom.val)).d g.1 :=
  congrArg (fun m ↦ m.hom.app U g)
    (moduleSheafFunctor_map_inverseImageIdealChain f A φ M b p DD hp)

/-- **The conormal chain identity on local sections, from the values of the morphism out of the
kernel ideal.** If a morphism out of the kernel ideal sends every local section to the value of a
derivation there, then its transport across the inverse image sends every local section of the
kernel ideal of the inverse image to the value of the transposed derivation. -/
lemma inverseImageIdealChain_app_of_sections
    (p : idealSheaf.{max u' v' w', v', u'} K (presentationRingHom.{max u' v' w', v', u'} K φ) ⟶
      (SheafOfModules.restrictScalars (presentationRingHom.{max u' v' w', v', u'} K φ)).obj
        ((directImageCommModules.{w, w', v, u, v', u'} f B).obj M))
    (DD : PresheafOfModulesOfCommRing.Derivation' (((SheafOfModules.restrictScalars
          (presentationRingHom.{max u' v' w', v', u'} K φ)).obj
        ((directImageCommModules.{w, w', v, u, v', u'} f B).obj M)).val) b.hom)
    (hps : ∀ (V : Dᵒᵖ) (t : ((idealSheaf.{max u' v' w', v', u'} K
        (presentationRingHom.{max u' v' w', v', u'} K φ)).val.obj V)),
      p.val.app V t =
        DD.d ((sectionOfIdealSheaf.{max u' v' w', v', u'} K φ V t : A.obj.obj V)))
    (U : Cᵒᵖ)
    (g : ((idealSheaf.{max u v w, v, u} J
      (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).val.obj U)) :
    (inverseImageIdealTransportEquiv f φ M (inverseImageIdealAdjunctionEquiv f φ M
        (conormalIdealDirectImageRestrictEquiv f φ M p))).val.app U g =
      ((inverseImageDerivationEquiv f b ((SheafOfModules.restrictScalars
            (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).obj M)).symm
          (DD.postcomp (directImageRestrictScalarsIso f φ M).hom.val)).d g.1 := by
  have hp0 : (Sheaf.moduleSheafFunctor
        (SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} A)).map p =
      (Sheaf.moduleSheafFunctor (SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} A)).map
          (SheafOfModules.kerIota (presentationModuleHom.{max u' v' w', v', u'} K
            (presentationRingHom.{max u' v' w', v', u'} K φ))) ≫
        derivationSheafHom b
          ((SheafOfModules.restrictScalars
            (presentationRingHom.{max u' v' w', v', u'} K φ)).obj
              ((directImageCommModules.{w, w', v, u, v', u'} f B).obj M)) DD := by
    refine Sheaf.hom_ext_sections fun V t ↦ ?_
    refine Eq.trans ?_ ((Sheaf.sectionsFunctor K V).map_comp_apply _ _ t).symm
    refine Eq.trans (sectionsFunctor_map_moduleSheafFunctor_map p V t) ?_
    refine Eq.trans ?_ (sectionsFunctor_map_derivationSheafHom b _ DD V _).symm
    rw [sectionsFunctor_map_moduleSheafFunctor_map_kerIota]
    exact (hps V t).trans rfl
  exact inverseImageIdealChain_app f A φ M b p DD
    (inverseImageIdealChain_hypothesis f A φ M b p DD hp0) U g

variable [Presheaf.IsLocallySurjective K φ.hom]

/-- **The six-step identification of the morphisms out of the two conormal sheaves, read on a
local section of the kernel ideal of the inverse image.** If the restriction to the kernel ideal
of the transpose of a morphism out of the inverse image of the conormal sheaf sends every local
section to the value of a derivation there, then the morphism out of the kernel ideal of the
inverse image which the identification produces sends every local section to the value of the
transposed derivation. -/
lemma conormalInverseImageIdealSheafEquiv_app_of_sections
    (x : (inverseImageCommModules.{w, w', v, u, v', u'} f B).obj
      (conormalModule.{max u' v' w', v', u'} K φ) ⟶ M)
    (DD : PresheafOfModulesOfCommRing.Derivation' (((SheafOfModules.restrictScalars
          (presentationRingHom.{max u' v' w', v', u'} K φ)).obj
        ((directImageCommModules.{w, w', v, u, v', u'} f B).obj M)).val) b.hom)
    (hps : ∀ (V : Dᵒᵖ) (t : ((idealSheaf.{max u' v' w', v', u'} K
        (presentationRingHom.{max u' v' w', v', u'} K φ)).val.obj V)),
      (conormalDirectImageIdealEquiv f φ M
          (conormalInverseImageAdjunctionEquiv f φ M x)).val.app V t =
        DD.d ((sectionOfIdealSheaf.{max u' v' w', v', u'} K φ V t : A.obj.obj V)))
    (U : Cᵒᵖ)
    (g : ((idealSheaf.{max u v w, v, u} J
      (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).val.obj U)) :
    (conormalInverseImageIdealSheafEquiv f φ M x).val.app U g =
      ((inverseImageDerivationEquiv f b ((SheafOfModules.restrictScalars
            (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).obj M)).symm
          (DD.postcomp (directImageRestrictScalarsIso f φ M).hom.val)).d g.1 :=
  inverseImageIdealChain_app_of_sections.{w, w', v, u, v', u'} f A φ M b _ DD hps U g

end ChainConsumers

section ConormalInverseImageDesc

universe w w' v u v' u'

open CategoryTheory AlgebraicGeometry.SheafOfModules
open Stacks.Sites.Conormal

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{max u' v' w'})]
  (f : MorphismOfTopoi (Sheaf J (Type (max u v w))) (Sheaf K (Type (max u' v' w'))))
  {A B : Sheaf K CommRingCat.{max u' v' w'}} (φ : A ⟶ B)
  [Presheaf.IsLocallySurjective K φ.hom]
  (M : SheafOfModules.{max u v w}
    (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj B)))

/-- **The identification of the morphisms out of the two conormal sheaves, recognised by the
universal property of the conormal sheaf of the inverse image.** A morphism out of the conormal
sheaf of `f⁻¹φ` whose restriction to the kernel ideal is the transport of `y` along the first
five steps of the identification is the image of `y` under the identification. This is the last
step read backwards, and it is stated here because the two equalities it relates are the two
spellings the consumers of the identification present. -/
lemma inverseImageConormalHomEquiv_eq_of
    (y : (inverseImageCommModules.{w, w', v, u, v', u'} f B).obj
      (conormalModule.{w', v', u'} K φ) ⟶ M)
    (z : conormalModule.{w, v, u} J (f.inverseImageRing.map φ) ⟶ M)
    (hz : conormalModuleHomEquivOf.{w, v, u} J (f.inverseImageRing.map φ)
          (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)
          (inverseImageRingMap_presentationRingHom.{w, w', v, u, v', u'} f φ) M z =
        conormalInverseImageIdealSheafEquiv.{w, w', v, u, v', u'} f φ M y) :
    inverseImageConormalHomEquiv.{w, w', v, u, v', u'} f φ M y = z := by
  have key : inverseImageConormalHomEquiv.{w, w', v, u, v', u'} f φ M y =
      inverseImageConormalDescEquiv.{w, w', v, u, v', u'} f φ M
        (conormalInverseImageIdealSheafEquiv.{w, w', v, u, v', u'} f φ M y) :=
    Equiv.trans_apply (conormalInverseImageIdealSheafEquiv.{w, w', v, u, v', u'} f φ M)
      (inverseImageConormalDescEquiv.{w, w', v, u, v', u'} f φ M) y
  exact key.trans ((Equiv.symm_apply_eq (conormalModuleHomEquivOf.{w, v, u} J
    (f.inverseImageRing.map φ) (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)
    (inverseImageRingMap_presentationRingHom.{w, w', v, u, v', u'} f φ) M)).mpr hz.symm)

end ConormalInverseImageDesc

end Stacks.Sheaves.RingedToposModules

namespace Stacks.SheafOfModules

section InverseImageNaiveCotangentSquareSections

universe u v w u' v' w'

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.SheafOfModules
open Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPullback
open Stacks.Sheaves.ToposPushforward
open CategoryTheory.Sheaf (inverseImageTargetModules)

attribute [local implicit_reducible] CategoryTheory.sheafCompose

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasWeakSheafify J CommRingCat.{max u v w}] [HasWeakSheafify K CommRingCat.{max u' v' w'}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u' v' w'} RingCat.{max u' v' w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{max u' v' w'})]
  (f : MorphismOfTopoi (Sheaf J (Type (max u v w))) (Sheaf K (Type (max u' v' w'))))
  {A B : Sheaf K CommRingCat.{max u' v' w'}} (a : A ⟶ B)

/-- **The conormal differential of the canonical presentation, restricted to the kernel ideal, is
the kernel inclusion followed by the derivation it represents**, as morphisms of the underlying
sheaves of sets. This is
`Stacks.SheafOfModules.conormalModuleHomEquivOf_canonicalConormalDifferential_app` read as an
identity of morphisms rather than of values on local sections. -/
lemma moduleSheafFunctor_map_canonicalConormalDifferential
    (N : _root_.SheafOfModules.{max u' v' w'} (Stacks.SheafOfModules.Tensor.ringSheaf B))
    (h : (canonicalConormalSequence.{v', u', max u' v' w', max u' v' w'} K A B a).X₂ ⟶ N) :
    (Sheaf.moduleSheafFunctor (Tensor.ringSheaf.{u', v', max u' v' w'}
          (freeAlgebraSheaf K A (underlyingPresheaf K B)))).map
        (conormalModuleHomEquivOf.{max u' v' w', v', u'} K (canonicalPresentation K A B a)
          (presentationRingHom.{max u' v' w', v', u'} K (canonicalPresentation K A B a)) rfl N
          (canonicalConormalDifferential.{u', v', w'} K A B a ≫ h)) =
      (Sheaf.moduleSheafFunctor (Tensor.ringSheaf.{u', v', max u' v' w'}
            (freeAlgebraSheaf K A (underlyingPresheaf K B)))).map
          (SheafOfModules.kerIota (presentationModuleHom.{max u' v' w', v', u'} K
            (presentationRingHom.{max u' v' w', v', u'} K (canonicalPresentation K A B a)))) ≫
        derivationSheafHom (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B))
          ((_root_.SheafOfModules.restrictScalars
            (presentationRingHom.{max u' v' w', v', u'} K
              (canonicalPresentation K A B a))).obj N)
          (naiveCotangentZeroDerivationEquiv.{u', v', w'} K A B a N h) := by
  refine Sheaf.hom_ext_sections fun U s ↦ ?_
  refine Eq.trans ?_ ((Sheaf.sectionsFunctor K U).map_comp_apply _ _ s).symm
  refine Eq.trans (sectionsFunctor_map_moduleSheafFunctor_map _ U s) ?_
  refine Eq.trans ?_ (sectionsFunctor_map_derivationSheafHom
    (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B)) _
    (naiveCotangentZeroDerivationEquiv.{u', v', w'} K A B a N h) U _).symm
  rw [sectionsFunctor_map_moduleSheafFunctor_map_kerIota]
  have key := conormalModuleHomEquivOf_canonicalConormalDifferential_app K A B a N h U s
  exact key.trans rfl

omit [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{max u' v' w'})] in
/-- `Stacks.SheafOfModules.inverseImageNaiveCotangentZeroIso_derivation` at the spelling of the
coefficient ring sheaf in which the degree `0` comparison is
`Stacks.SheafOfModules.inverseImageNaiveCotangentZeroTargetIso`. -/
lemma inverseImageNaiveCotangentZeroTargetIso_derivation :
    inverseImageNaiveCotangentZeroDerivationEquiv J K f a
        (canonicalConormalSequence.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A)
          (f.inverseImageRing.obj B) (f.inverseImageRing.map a)).X₂
        (inverseImageNaiveCotangentZeroTargetIso J K f a).hom =
      naiveCotangentZeroDerivationEquiv.{u, v, w} J (f.inverseImageRing.obj A)
        (f.inverseImageRing.obj B) (f.inverseImageRing.map a) _ (𝟙 _) :=
  inverseImageNaiveCotangentZeroIso_derivation J K f a

omit [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{max u' v' w'})] in
/-- **The `f⁻¹A`-derivation of the degree `0` comparison, evaluated at a local section of
`f⁻¹(A[B])`.** Transposing the degree `0` comparison across `f⁻¹ ⊣ f_*` and the exchange of the
direct image with restriction of scalars gives the derivation whose value at a local section `p`
of `f⁻¹(A[B])` is the local section `1 ⊗ dp` of the degree `0` term of the naive cotangent
complex of `f⁻¹a`, read at the image of `p` under `f⁻¹(A[B]) ≅ (f⁻¹A)[f⁻¹B]`. -/
lemma inverseImageNaiveCotangentZeroDerivation_d (U : Cᵒᵖ)
    (z : (f.inverseImageRing.obj
      (freeAlgebraSheaf K A (underlyingPresheaf K B))).obj.obj U) :
    (inverseImageZeroStep₄ J K f a
        (canonicalConormalSequence.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A)
          (f.inverseImageRing.obj B) (f.inverseImageRing.map a)).X₂
      (inverseImageZeroStep₃ J K f a
        (canonicalConormalSequence.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A)
          (f.inverseImageRing.obj B) (f.inverseImageRing.map a)).X₂
        (pushforwardZeroDerivation J K f a
          (canonicalConormalSequence.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A)
            (f.inverseImageRing.obj B) (f.inverseImageRing.map a)).X₂
          (inverseImageNaiveCotangentZeroTargetIso J K f a).hom))).d z =
      tensorDifferential.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A)
        (freeAlgebraSheaf J (f.inverseImageRing.obj A)
          (underlyingPresheaf J (f.inverseImageRing.obj B))) (f.inverseImageRing.obj B)
        (freeAlgebraSheafCoefficientMap J (f.inverseImageRing.obj A)
          (underlyingPresheaf J (f.inverseImageRing.obj B)))
        (canonicalPresentation J (f.inverseImageRing.obj A) (f.inverseImageRing.obj B)
          (f.inverseImageRing.map a)) U
        ((inverseImageFreeAlgebraIso f A B).hom.hom.app U z) := by
  have h1 := inverseImageNaiveCotangentZeroDerivationEquiv_d_freeAlgebraIso J K f a
    (canonicalConormalSequence.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A)
      (f.inverseImageRing.obj B) (f.inverseImageRing.map a)).X₂
    (inverseImageNaiveCotangentZeroTargetIso J K f a).hom U z
  refine h1.symm.trans ?_
  rw [inverseImageNaiveCotangentZeroTargetIso_derivation]
  have h3 := naiveCotangentZeroDerivationEquiv_d J (f.inverseImageRing.obj A)
    (f.inverseImageRing.obj B) (f.inverseImageRing.map a)
    (canonicalConormalSequence.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A)
      (f.inverseImageRing.obj B) (f.inverseImageRing.map a)).X₂ (𝟙 _) U
    ((inverseImageFreeAlgebraIso f A B).hom.hom.app U z)
  exact h3.trans rfl

omit [K.HasSheafCompose (forget₂ CommRingCat.{max u' v' w'} RingCat.{max u' v' w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{max u' v' w'})] in
/-- **The degree `-1` comparison followed by the conormal differential, restricted to the kernel
ideal and read on local sections.** It sends a local section `g` of `Ker(f⁻¹φ)` to the local
section `1 ⊗ dg` of the degree `0` term of the naive cotangent complex of `f⁻¹a`, read at the
image of `g` under `f⁻¹(A[B]) ≅ (f⁻¹A)[f⁻¹B]`. Together with
`Stacks.SheafOfModules.inverseImageNaiveCotangentZeroDerivation_d` this is the commutation of the
two comparisons of Stacks 08TZ with the two conormal differentials, read on local sections. -/
lemma conormalModuleHomEquivOf_inverseImagePresentationConormalIso_app (U : Cᵒᵖ)
    (g : ((idealSheaf.{max u v w, v, u} J
      (inverseImagePresentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f
        (canonicalPresentation K A B a))).val.obj U)) :
    (conormalModuleHomEquivOf.{max u v w, v, u} J
        (f.inverseImageRing.map (canonicalPresentation K A B a))
        (inverseImagePresentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f
          (canonicalPresentation K A B a))
        (inverseImageRingMap_presentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f
          (canonicalPresentation K A B a))
        (canonicalConormalSequence.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A)
          (f.inverseImageRing.obj B) (f.inverseImageRing.map a)).X₂
        ((inverseImagePresentationConormalIso J K f a).hom ≫
          (canonicalConormalSequence.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A)
            (f.inverseImageRing.obj B) (f.inverseImageRing.map a)).f)).val.app U g =
      tensorDifferential.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A)
        (freeAlgebraSheaf J (f.inverseImageRing.obj A)
          (underlyingPresheaf J (f.inverseImageRing.obj B))) (f.inverseImageRing.obj B)
        (freeAlgebraSheafCoefficientMap J (f.inverseImageRing.obj A)
          (underlyingPresheaf J (f.inverseImageRing.obj B)))
        (canonicalPresentation J (f.inverseImageRing.obj A) (f.inverseImageRing.obj B)
          (f.inverseImageRing.map a)) U
        ((inverseImageFreeAlgebraIso f A B).hom.hom.app U g.1) := by
  have hy := coe_mem_kernelIdeal.{max u v w, v, u} J
    (f.inverseImageRing.map (canonicalPresentation K A B a))
    (inverseImagePresentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f
      (canonicalPresentation K A B a))
    (inverseImageRingMap_presentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f
      (canonicalPresentation K A B a)) U g
  have h1 := conormalModuleHomEquivOf_app_conormalClass.{max u v w, v, u} J
    (f.inverseImageRing.map (canonicalPresentation K A B a))
    (inverseImagePresentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f
      (canonicalPresentation K A B a))
    (inverseImageRingMap_presentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f
      (canonicalPresentation K A B a))
    (f.inverseImageRing.obj A)
    (f.inverseImageRing.map (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B)))
    (canonicalConormalSequence.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A)
      (f.inverseImageRing.obj B) (f.inverseImageRing.map a)).X₂
    ((inverseImagePresentationConormalIso J K f a).hom ≫
      (canonicalConormalSequence.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A)
        (f.inverseImageRing.obj B) (f.inverseImageRing.map a)).f) U g ⟨g.1, hy⟩ rfl
  refine h1.trans ?_
  simp only [inverseImagePresentationConormalIso]
  have h2 := conormalSheafMapOfFac_conormalClass (J := J) (R := f.inverseImageRing.obj A)
    (B := f.inverseImageRing.obj B)
    (A₁ := f.inverseImageRing.obj (freeAlgebraSheaf K A (underlyingPresheaf K B)))
    (A₂ := freeAlgebraSheaf J (f.inverseImageRing.obj A)
      (underlyingPresheaf J (f.inverseImageRing.obj B)))
    (a₁ := f.inverseImageRing.map (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B)))
    (a₂ := freeAlgebraSheafCoefficientMap J (f.inverseImageRing.obj A)
      (underlyingPresheaf J (f.inverseImageRing.obj B)))
    (φ₁ := f.inverseImageRing.map (canonicalPresentation K A B a))
    (φ₂ := canonicalPresentation J (f.inverseImageRing.obj A) (f.inverseImageRing.obj B)
      (f.inverseImageRing.map a))
    (ψ := (inverseImageFreeAlgebraIso f A B).hom)
    (hψ := inverseImageFreeAlgebraHom_comp_canonicalPresentation f A B a)
    (X := U) (x := ⟨g.1, hy⟩)
  refine (congrArg (fun y ↦ (canonicalConormalSequence.{v, u, max u v w, max u v w} J
    (f.inverseImageRing.obj A) (f.inverseImageRing.obj B)
    (f.inverseImageRing.map a)).f.val.app U y) h2).trans ?_
  exact conormalSequence_f_class.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A)
    (freeAlgebraSheaf J (f.inverseImageRing.obj A)
      (underlyingPresheaf J (f.inverseImageRing.obj B))) (f.inverseImageRing.obj B)
    (freeAlgebraSheafCoefficientMap J (f.inverseImageRing.obj A)
      (underlyingPresheaf J (f.inverseImageRing.obj B)))
    (canonicalPresentation J (f.inverseImageRing.obj A) (f.inverseImageRing.obj B)
      (f.inverseImageRing.map a)) U _

omit [HasWeakSheafify J CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u' v' w'} RingCat.{max u' v' w'})] in
/-- **Transposing the inverse image of the conormal differential across `f⁻¹ ⊣ f_*`.** A morphism
out of the inverse image of the degree `0` term, precomposed with the inverse image of the
conormal differential of the canonical presentation, transposes to the conormal differential
followed by the transpose of that morphism. This is naturality of the hom-set bijection of
Stacks 03D3 in the source, read at the conormal differential; it identifies the morphism out of
the kernel ideal that the degree `-1` chain of Stacks 08TZ produces with the one
`Stacks.SheafOfModules.moduleSheafFunctor_map_canonicalConormalDifferential` computes. -/
lemma conormalInverseImageAdjunctionEquiv_canonicalConormalDifferential_comp
    (M : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B)))
    (h : (inverseImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'} B)).obj
        (canonicalConormalSequence.{v', u', max u' v' w', max u' v' w'} K A B a).X₂ ⟶ M) :
    conormalInverseImageAdjunctionEquiv.{max u v w, max u' v' w', v, u, v', u'} f
        (canonicalPresentation K A B a) M
        ((inverseImageTargetModules.{u, v, w, u', v', w'} J K f (B := B)).map
            (canonicalConormalDifferential.{u', v', w'} K A B a) ≫ h) =
      canonicalConormalDifferential.{u', v', w'} K A B a ≫
        inverseImageZeroStep₁ J K f a M h := by
  have hmk : (commModulesAdjunction.{max u v w, max u' v' w', v, u, v', u'} f B).homEquiv =
      toposModulesHomEquiv f (Tensor.ringSheaf.{u', v', max u' v' w'} B) :=
    Adjunction.mkOfHomEquiv_homEquiv _
  have hstepL := congrArg (fun e ↦ e
    (conormalModule.{max u' v' w', v', u'} K (canonicalPresentation K A B a)) M
    ((inverseImageTargetModules.{u, v, w, u', v', w'} J K f (B := B)).map
      (canonicalConormalDifferential.{u', v', w'} K A B a) ≫ h)) hmk
  have hnatT := toposModulesHomEquiv_naturality_left f
    (Tensor.ringSheaf.{u', v', max u' v' w'} B)
    (canonicalConormalDifferential.{u', v', w'} K A B a) h
  exact hstepL.trans hnatT

omit [HasWeakSheafify J CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})] in
/-- **The third and fourth steps of the degree `0` chain, read on a local section.** The
transposition across `f⁻¹ ⊣ f_*` of a derivation whose scalars have been exchanged with the
direct image is, on local sections, the composite
`Stacks.SheafOfModules.inverseImageZeroStep₄ ∘ Stacks.SheafOfModules.inverseImageZeroStep₃`.
This is the spelling in which the value produced by
`Stacks.Sheaves.RingedToposModules.inverseImageIdealChain_app_of_sections` meets the value
`Stacks.SheafOfModules.inverseImageNaiveCotangentZeroDerivation_d` computes. -/
lemma inverseImageDerivationEquiv_symm_postcomp_d
    (M : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B)))
    (DD : PresheafOfModulesOfCommRing.Derivation' (((_root_.SheafOfModules.restrictScalars
          (presentationRingHom.{max u' v' w', v', u'} K (canonicalPresentation K A B a))).obj
        ((directImageCommModules.{max u v w, max u' v' w', v, u, v', u'} f B).obj
          M)).val)
        (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B)).hom)
    {U : Cᵒᵖ}
    (z : (f.inverseImageRing.obj
      (freeAlgebraSheaf K A (underlyingPresheaf K B))).obj.obj U) :
    ((inverseImageDerivationEquiv f
          (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B))
          ((_root_.SheafOfModules.restrictScalars
            (inverseImagePresentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f
              (canonicalPresentation K A B a))).obj M)).symm
        (DD.postcomp
          (directImageRestrictScalarsIso f (canonicalPresentation K A B a) M).hom.val)).d z =
      (inverseImageZeroStep₄ J K f a M (inverseImageZeroStep₃ J K f a M DD)).d z :=
  rfl

omit [HasWeakSheafify J CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})] in
/-- **The restriction to the kernel ideal of the transpose of the degree `-1` comparison
followed by a morphism out of the degree `0` term, read on a local section.** It is the value
there of the `A`-derivation of `A[B]` attached to that morphism. This is the hypothesis of the
conormal chain identity at the canonical presentation. -/
lemma conormalDirectImageIdealEquiv_canonicalConormalDifferential_app
    (M : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B)))
    (h : (inverseImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'} B)).obj
        (canonicalConormalSequence.{v', u', max u' v' w', max u' v' w'} K A B a).X₂ ⟶ M)
    (V : Dᵒᵖ)
    (t : ((idealSheaf.{max u' v' w', v', u'} K
      (presentationRingHom.{max u' v' w', v', u'} K
        (canonicalPresentation K A B a))).val.obj V)) :
    (conormalDirectImageIdealEquiv.{max u v w, max u' v' w', v, u, v', u'} f
        (canonicalPresentation K A B a) M
        (conormalInverseImageAdjunctionEquiv.{max u v w, max u' v' w', v, u, v', u'} f
          (canonicalPresentation K A B a) M
          ((inverseImageTargetModules.{u, v, w, u', v', w'} J K f (B := B)).map
              (canonicalConormalDifferential.{u', v', w'} K A B a) ≫ h))).val.app V t =
      (pushforwardZeroDerivation.{u, v, w, u', v', w'} J K f a M h).d
        ((sectionOfIdealSheaf.{max u' v' w', v', u'} K (canonicalPresentation K A B a) V t :
          (freeAlgebraSheaf K A (underlyingPresheaf K B)).obj.obj V)) := by
  have hstep := conormalInverseImageAdjunctionEquiv_canonicalConormalDifferential_comp.{u, v, w,
    u', v', w'} J K f a M h
  have key := conormalModuleHomEquivOf_canonicalConormalDifferential_app.{u', v', w'} K A B a
    ((directImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'} B)).obj M)
    (inverseImageZeroStep₁.{u, v, w, u', v', w'} J K f a M h) V t
  exact (congrArg (fun q ↦ (conormalDirectImageIdealEquiv.{max u v w, max u' v' w', v, u, v',
    u'} f (canonicalPresentation K A B a) M q).val.app V t) hstep).trans key

omit [HasWeakSheafify J CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})] in
/-- **The degree `-1` comparison followed by the conormal differential, transported to the
kernel ideal of the inverse image and read on a local section.** It is the value there of the
`f⁻¹A`-derivation of `(f⁻¹A)[f⁻¹B]` which the degree `0` chain attaches to the same morphism.
This is the identity of the two chains of bijections of Stacks 08TZ at the canonical
presentation. -/
lemma conormalInverseImageIdealSheafEquiv_canonicalConormalDifferential_app
    (M : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B)))
    (h : (inverseImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'} B)).obj
        (canonicalConormalSequence.{v', u', max u' v' w', max u' v' w'} K A B a).X₂ ⟶ M)
    (U : Cᵒᵖ)
    (g : ((idealSheaf.{max u v w, v, u} J
      (inverseImagePresentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f
        (canonicalPresentation K A B a))).val.obj U)) :
    (conormalInverseImageIdealSheafEquiv.{max u v w, max u' v' w', v, u, v', u'} f
        (canonicalPresentation K A B a) M
        ((inverseImageTargetModules.{u, v, w, u', v', w'} J K f (B := B)).map
            (canonicalConormalDifferential.{u', v', w'} K A B a) ≫ h)).val.app U g =
      (inverseImageZeroStep₄.{u, v, w, u', v', w'} J K f a M
        (inverseImageZeroStep₃.{u, v, w, u', v', w'} J K f a M
          (pushforwardZeroDerivation.{u, v, w, u', v', w'} J K f a M h))).d g.1 := by
  have main := conormalInverseImageIdealSheafEquiv_app_of_sections.{max u v w, max u' v' w', v, u,
      v', u'} f (freeAlgebraSheaf K A (underlyingPresheaf K B)) (canonicalPresentation K A B a) M
    (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B))
    ((inverseImageTargetModules.{u, v, w, u', v', w'} J K f (B := B)).map
      (canonicalConormalDifferential.{u', v', w'} K A B a) ≫ h)
    (pushforwardZeroDerivation.{u, v, w, u', v', w'} J K f a M h)
    (conormalDirectImageIdealEquiv_canonicalConormalDifferential_app.{u, v, w, u', v', w'}
      J K f a M h) U g
  have post := inverseImageDerivationEquiv_symm_postcomp_d.{u, v, w, u', v', w'} J K f a M
    (pushforwardZeroDerivation.{u, v, w, u', v', w'} J K f a M h) g.1
  exact main.trans post

omit [HasWeakSheafify J CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})] in
/-- **Both chains of bijections of Stacks 08TZ produce the same morphism out of the kernel ideal
of the inverse image**, once a morphism out of the conormal sheaf of `f⁻¹(A[B] ⟶ B)` is known to
restrict to the kernel ideal as the derivation the degree `0` chain transposes to. The two sides
are morphisms of sheaves of modules and are compared on local sections. -/
lemma conormalModuleHomEquivOf_eq_conormalInverseImageIdealSheafEquiv
    (M : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B)))
    (h : (inverseImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'} B)).obj
        (canonicalConormalSequence.{v', u', max u' v' w', max u' v' w'} K A B a).X₂ ⟶ M)
    (z : conormalModule.{max u v w, v, u} J
      (f.inverseImageRing.map (canonicalPresentation K A B a)) ⟶ M)
    (hz : ∀ (U : Cᵒᵖ) (g : ((idealSheaf.{max u v w, v, u} J
        (inverseImagePresentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f
          (canonicalPresentation K A B a))).val.obj U)),
      (conormalModuleHomEquivOf.{max u v w, v, u} J
          (f.inverseImageRing.map (canonicalPresentation K A B a))
          (inverseImagePresentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f
            (canonicalPresentation K A B a))
          (inverseImageRingMap_presentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f
            (canonicalPresentation K A B a)) M z).val.app U g =
        (inverseImageZeroStep₄.{u, v, w, u', v', w'} J K f a M
          (inverseImageZeroStep₃.{u, v, w, u', v', w'} J K f a M
            (pushforwardZeroDerivation.{u, v, w, u', v', w'} J K f a M h))).d g.1) :
    conormalModuleHomEquivOf.{max u v w, v, u} J
        (f.inverseImageRing.map (canonicalPresentation K A B a))
        (inverseImagePresentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f
          (canonicalPresentation K A B a))
        (inverseImageRingMap_presentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f
          (canonicalPresentation K A B a)) M z =
      conormalInverseImageIdealSheafEquiv.{max u v w, max u' v' w', v, u, v', u'} f
        (canonicalPresentation K A B a) M
        ((inverseImageTargetModules.{u, v, w, u', v', w'} J K f (B := B)).map
          (canonicalConormalDifferential.{u', v', w'} K A B a) ≫ h) := by
  refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦
    ModuleCat.hom_ext (LinearMap.ext fun g ↦ ?_))
  have l := hz U g
  have r := conormalInverseImageIdealSheafEquiv_canonicalConormalDifferential_app.{u, v, w, u',
    v', w'} J K f a M h U g
  exact l.trans r.symm

/-- **The two comparisons of Stacks 08TZ commute with the two conormal differentials.** The
degree `-1` comparison followed by the conormal differential of the canonical presentation of
`f⁻¹B` is the inverse image of the conormal differential of the canonical presentation of `B`
followed by the degree `0` comparison. Both send a local section `g` of `Ker(f⁻¹(A[B] ⟶ B))` to
the local section `1 ⊗ dg`, which is what
`Stacks.SheafOfModules.conormalModuleHomEquivOf_inverseImagePresentationConormalIso_app` and
`Stacks.SheafOfModules.inverseImageNaiveCotangentZeroDerivation_d` compute; the identity of
morphisms follows because the degree `-1` comparison is the Yoneda transport of a natural family
of bijections and because the conormal sheaf of the inverse image is determined by the morphisms
out of its kernel ideal. -/
theorem inverseImageNaiveCotangentSquare :
    InverseImageNaiveCotangentSquare.{u, v, w, u', v', w'} J K f a := by
  have hz := conormalModuleHomEquivOf_eq_conormalInverseImageIdealSheafEquiv.{u, v, w, u', v',
      w'} J K f a
    (canonicalConormalSequence.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A)
      (f.inverseImageRing.obj B) (f.inverseImageRing.map a)).X₂
    (inverseImageNaiveCotangentZeroTargetIso.{u, v, w, u', v', w'} J K f a).hom
    ((inverseImagePresentationConormalIso.{u, v, w, u', v', w'} J K f a).hom ≫
      (canonicalConormalSequence.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A)
        (f.inverseImageRing.obj B) (f.inverseImageRing.map a)).f)
    (fun U g ↦
      (conormalModuleHomEquivOf_inverseImagePresentationConormalIso_app.{u, v, w, u', v', w'}
          J K f a U g).trans
        (inverseImageNaiveCotangentZeroDerivation_d.{u, v, w, u', v', w'} J K f a U g.1).symm)
  have hv := inverseImageConormalHomEquiv_eq_of.{max u v w, max u' v' w', v, u, v', u'} f
    (canonicalPresentation K A B a)
    (canonicalConormalSequence.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A)
      (f.inverseImageRing.obj B) (f.inverseImageRing.map a)).X₂
    ((inverseImageTargetModules.{u, v, w, u', v', w'} J K f (B := B)).map
      (canonicalConormalDifferential.{u', v', w'} K A B a) ≫
      (inverseImageNaiveCotangentZeroTargetIso.{u, v, w, u', v', w'} J K f a).hom)
    ((inverseImagePresentationConormalIso.{u, v, w, u', v', w'} J K f a).hom ≫
      (canonicalConormalSequence.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A)
        (f.inverseImageRing.obj B) (f.inverseImageRing.map a)).f) hz
  have final := isoOfNaturalHomEquiv_hom_comp
    (inverseImageConormalHomEquiv.{max u v w, max u' v' w', v, u, v', u'} f
      (canonicalPresentation K A B a))
    (naturalHomEquiv_inverseImageConormalHomEquiv.{max u v w, max u' v' w', v, u, v', u'} f
      (canonicalPresentation K A B a))
    (canonicalConormalSequence.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A)
      (f.inverseImageRing.obj B) (f.inverseImageRing.map a)).X₂
    ((inverseImageTargetModules.{u, v, w, u', v', w'} J K f (B := B)).map
      (canonicalConormalDifferential.{u', v', w'} K A B a) ≫
      (inverseImageNaiveCotangentZeroTargetIso.{u, v, w, u', v', w'} J K f a).hom)
    ((inverseImagePresentationConormalIso.{u, v, w, u', v', w'} J K f a).hom ≫
      (canonicalConormalSequence.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A)
        (f.inverseImageRing.obj B) (f.inverseImageRing.map a)).f) hv
  exact (Category.assoc _ _ _).trans final

/-- **The inverse image of the naive cotangent complex is the naive cotangent complex of the
inverse image**: `f⁻¹ NL_{B/A} ≅ NL_{f⁻¹B/f⁻¹A}`, as an isomorphism of two-term complexes of
sheaves of `f⁻¹B`-modules, with the identification of the degree `-1` terms in degree `-1` and
the identification of the degree `0` terms in degree `0`. -/
@[stacks 08TZ "the inverse image of the naive cotangent complex is the naive cotangent \
complex of the inverse image, as an isomorphism of complexes: the identification the tag \
states, assembled from the degree -1 and the degree 0 comparison and their commutation with \
the conormal differentials"]
noncomputable def inverseImageNaiveCotangentComplexIso :
    ((inverseImageTargetModules.{u, v, w, u', v', w'} J K f
            (B := B)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (naiveCotangentComplex.{v', u', max u' v' w', max u' v' w'} K A B a) ≅
      naiveCotangentComplex.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A)
        (f.inverseImageRing.obj B) (f.inverseImageRing.map a) := by
  letI : HasZeroObject
      (_root_.SheafOfModules.{max u' v' w'} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  letI : HasZeroObject
      (_root_.SheafOfModules.{max u v w}
        (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B))) :=
    hasZeroObject_of_hasTerminal_object
  refine HomologicalComplex.isoFromMapDouble
    (inverseImageTargetModules.{u, v, w, u', v', w'} J K f (B := B))
    (canonicalConormalSequence.{v', u', max u' v' w', max u' v' w'} K A B a).f
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)
    ((inverseImageNaiveCotangentNegOneIso J K f a).trans
      (naiveCotangentComplexXNegOneIso.{u, v, max u v w, max u v w} J
        (f.inverseImageRing.obj A) (f.inverseImageRing.obj B)
        (f.inverseImageRing.map a)).symm)
    ((inverseImageNaiveCotangentZeroTargetIso J K f a).trans
      (naiveCotangentComplexXZeroIso.{u, v, max u v w, max u v w} J
        (f.inverseImageRing.obj A) (f.inverseImageRing.obj B)
        (f.inverseImageRing.map a)).symm) ?_ ?_ ?_
  · rw [naiveCotangentComplex_d_negOne_zero_iso.{u, v, max u v w, max u v w} J
      (f.inverseImageRing.obj A) (f.inverseImageRing.obj B) (f.inverseImageRing.map a)]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
    have sq := inverseImageNaiveCotangentSquare.{u, v, w, u', v', w'} J K f a
    simpa only [Category.assoc] using congrArg (fun t ↦ t ≫
      (naiveCotangentComplexXZeroIso.{u, v, max u v w, max u v w} J (f.inverseImageRing.obj A)
        (f.inverseImageRing.obj B) (f.inverseImageRing.map a)).inv) sq
  · intro k _
    rw [naiveCotangentComplex_d_zero_eq_zero.{u, v, max u v w, max u v w} J
      (f.inverseImageRing.obj A) (f.inverseImageRing.obj B) (f.inverseImageRing.map a) k,
      Limits.comp_zero]
  · intro k h₀ h₁
    exact naiveCotangentComplex_isZero_X.{v, u, max u v w, max u v w} J
      (f.inverseImageRing.obj A) (f.inverseImageRing.obj B) (f.inverseImageRing.map a) k h₀ h₁

end InverseImageNaiveCotangentSquareSections

end Stacks.SheafOfModules

end
