module

public import StacksFrontier.CategoryTheory.Homology.HomFromMapDouble
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalPresentationIso
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentInverseImageNaturality

/-!
# The degree-wise comparisons of the inverse image of the naive cotangent complex

The Yoneda bookkeeping for natural families of bijections of morphisms, the identity of the
conormal chain across the inverse image (restricting a derivation to the kernel ideal commutes
with the transport across `f⁻¹ ⊣ f_*`), the universal property of the degree-`0` term of the
naive cotangent complex on sections, the comparison isomorphisms of the two terms of the
two-term complex, and the degree `-1` and degree `0` comparisons of Stacks 08TZ together with
the statement `Stacks.SheafOfModules.InverseImageNaiveCotangentSquare` of their commutation with
the conormal differentials.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.Sheaves.RingedToposModules

section YonedaHomEquiv

universe vv uu

variable {E : Type uu} [Category.{vv} E] {X Y : E}
  (e : ∀ Z : E, (X ⟶ Z) ≃ (Y ⟶ Z)) (he : NaturalHomEquiv e)

/-- The forward morphism of the isomorphism produced by the Yoneda argument is the inverse
image of the identity. -/
lemma isoOfNaturalHomEquiv_hom : (isoOfNaturalHomEquiv e he).hom = (e Y).symm (𝟙 Y) :=
  rfl

/-- The backward morphism of the isomorphism produced by the Yoneda argument is the image of
the identity. -/
lemma isoOfNaturalHomEquiv_inv : (isoOfNaturalHomEquiv e he).inv = e X (𝟙 X) :=
  rfl

/-- A natural family of bijections of the morphisms out of two objects is precomposition with
the backward morphism of the isomorphism it produces. -/
lemma isoOfNaturalHomEquiv_apply (Z : E) (x : X ⟶ Z) :
    e Z x = (isoOfNaturalHomEquiv e he).inv ≫ x := by
  rw [isoOfNaturalHomEquiv_inv, ← he X Z (𝟙 X) x, Category.id_comp]

/-- The inverse of a natural family of bijections of the morphisms out of two objects is
precomposition with the forward morphism of the isomorphism it produces. -/
lemma isoOfNaturalHomEquiv_symm_apply (Z : E) (y : Y ⟶ Z) :
    (e Z).symm y = (isoOfNaturalHomEquiv e he).hom ≫ y := by
  refine (e Z).injective ?_
  rw [Equiv.apply_symm_apply, isoOfNaturalHomEquiv_apply e he, Iso.inv_hom_id_assoc]

/-- **A morphism out of the second object is recovered from the bijection.** If the natural
family of bijections carries `x` to `y`, then precomposing `y` with the forward morphism of the
isomorphism the Yoneda argument produces gives `x` back. This is how an identity of morphisms
out of the second object becomes one out of the first. -/
lemma isoOfNaturalHomEquiv_hom_comp (Z : E) (x : X ⟶ Z) (y : Y ⟶ Z) (hxy : e Z x = y) :
    (isoOfNaturalHomEquiv e he).hom ≫ y = x := by
  rw [← hxy, isoOfNaturalHomEquiv_apply e he Z x, Iso.hom_inv_id_assoc]

end YonedaHomEquiv

section InverseImageIdealChain

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

/-- **Restricting a derivation to the kernel ideal commutes with the transport of the conormal
chain across the inverse image.** The last three steps of
`Stacks.Sheaves.RingedToposModules.conormalInverseImageIdealSheafEquiv` — the exchange of the
direct image with restriction of scalars, the transposition across the adjunction of
Stacks 03D3 and the identification `f⁻¹ℐ ≅ ℐ'` — carry the restriction to `ℐ` of a derivation
with values in a direct image to the restriction to `ℐ'` of its transpose. -/
lemma moduleSheafFunctor_map_inverseImageIdealChain
    (p : idealSheaf.{max u' v' w', v', u'} K (presentationRingHom.{max u' v' w', v', u'} K φ) ⟶
      (SheafOfModules.restrictScalars (presentationRingHom.{max u' v' w', v', u'} K φ)).obj
        ((directImageCommModules.{w, w', v, u, v', u'} f B).obj M))
    (DD : (((SheafOfModules.restrictScalars
          (presentationRingHom.{max u' v' w', v', u'} K φ)).obj
        ((directImageCommModules.{w, w', v, u, v', u'} f B).obj M)).val).Derivation' b.hom)
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
          (DD.postcomp (directImageRestrictScalarsIso f φ M).hom.val)) :
    (Sheaf.moduleSheafFunctor
          (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj A))).map
        (inverseImageIdealTransportEquiv f φ M (inverseImageIdealAdjunctionEquiv f φ M
          (conormalIdealDirectImageRestrictEquiv f φ M p))) =
      (Sheaf.moduleSheafFunctor
            (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj A))).map
          (SheafOfModules.kerIota (presentationModuleHom.{max u v w, v, u} J
            (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ))) ≫
        derivationSheafHom (f.inverseImageRing.map b) _
          ((inverseImageDerivationEquiv f b ((SheafOfModules.restrictScalars
              (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).obj M)).symm
            (DD.postcomp (directImageRestrictScalarsIso f φ M).hom.val)) := by
  have h2 := (derivationSheafHom_inverseImageDerivationEquiv f b
    ((SheafOfModules.restrictScalars
      (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).obj M)
    ((inverseImageDerivationEquiv f b ((SheafOfModules.restrictScalars
        (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).obj M)).symm
      (DD.postcomp (directImageRestrictScalarsIso f φ M).hom.val)))
  rw [Equiv.apply_symm_apply] at h2
  rw [inverseImageIdealTransportEquiv_apply, conormalIdealDirectImageRestrictEquiv_apply,
    CategoryTheory.Functor.map_comp,
    moduleSheafFunctor_map_inverseImageIdealAdjunctionEquiv,
    CategoryTheory.Functor.map_comp, hp]
  refine Eq.trans (whisker_eq _ (f.adj.homEquiv_naturality_left_symm _ _)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _ ((Equiv.symm_apply_eq _).mpr h2))) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  rw [moduleSheafFunctor_map_inverseImageIdealIso_inv_comp f A φ]
  rfl

end InverseImageIdealChain

end Stacks.Sheaves.RingedToposModules

namespace Stacks.SheafOfModules

section NaiveCotangentZeroSections

universe uu vv ww

open CategoryTheory AlgebraicGeometry.SheafOfModules Stacks.Sites.FreeAlgebra
open Stacks.Sites.Conormal

variable {C : Type uu} [Category.{vv} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{max uu vv ww}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max uu vv ww} RingCat.{max uu vv ww})]
  (A B : Sheaf J CommRingCat.{max uu vv ww}) (a : A ⟶ B)
  (N : _root_.SheafOfModules.{max uu vv ww} (Stacks.SheafOfModules.Tensor.ringSheaf B))

/-- The corepresentability step of the universal property of the degree-`0` term evaluates a
morphism out of the sheaf of relative differentials at the universal derivation. -/
lemma zeroDerivationStep₃_d
    (g : moduleOfDifferentialsOfSite.{vv, uu, max uu vv ww, max uu vv ww} A
          (freeAlgebraSheaf J A (underlyingPresheaf J B))
          (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B)) ⟶
        (_root_.SheafOfModules.pushforward
          (Stacks.Sites.Conormal.underlyingRingHomForPullback J
            (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
            (canonicalPresentation J A B a))).obj N)
    (U : Cᵒᵖ) (p : (freeAlgebraSheaf J A (underlyingPresheaf J B)).obj.obj U) :
    (zeroDerivationStep₃ J A B a N g).d p =
      g.val.app U ((universalDerivationOfSite.{vv, uu, max uu vv ww, max uu vv ww} A
        (freeAlgebraSheaf J A (underlyingPresheaf J B))
        (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))).d p) :=
  congrArg (fun DD ↦ DD.d p)
    ((derivationsFunctor.{max uu vv ww} A (freeAlgebraSheaf J A (underlyingPresheaf J B))
      (freeAlgebraSheafCoefficientMap J A
        (underlyingPresheaf J B))).corepresentableBy.homEquiv_eq g)

/-- The extension/restriction of scalars step of the universal property of the degree-`0` term
is evaluation after the unit of the adjunction. -/
lemma zeroDerivationStep₂_app
    (y : (_root_.SheafOfModules.pullback
          (Stacks.Sites.Conormal.underlyingRingHomForPullback J
            (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
            (canonicalPresentation J A B a))).obj
        (moduleOfDifferentialsOfSite.{vv, uu, max uu vv ww, max uu vv ww} A
          (freeAlgebraSheaf J A (underlyingPresheaf J B))
          (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))) ⟶ N)
    (U : Cᵒᵖ)
    (z : (moduleOfDifferentialsOfSite.{vv, uu, max uu vv ww, max uu vv ww} A
      (freeAlgebraSheaf J A (underlyingPresheaf J B))
      (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))).val.obj U) :
    (zeroDerivationStep₂ J A B a N y).val.app U z =
      y.val.app U (((_root_.SheafOfModules.pullbackPushforwardAdjunction
          (Stacks.Sites.Conormal.underlyingRingHomForPullback J
            (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
            (canonicalPresentation J A B a))).unit.app
        (moduleOfDifferentialsOfSite.{vv, uu, max uu vv ww, max uu vv ww} A
          (freeAlgebraSheaf J A (underlyingPresheaf J B))
          (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B)))).val.app U z) :=
  congrArg (fun t ↦ t.val.app U z)
    (Adjunction.homEquiv_unit (_root_.SheafOfModules.pullbackPushforwardAdjunction
      (Stacks.Sites.Conormal.underlyingRingHomForPullback J
        (freeAlgebraSheaf J A (underlyingPresheaf J B)) B (canonicalPresentation J A B a)))
      (X := moduleOfDifferentialsOfSite.{vv, uu, max uu vv ww, max uu vv ww} A
        (freeAlgebraSheaf J A (underlyingPresheaf J B))
        (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))) (Y := N) (f := y))

/-- The comparison of the degree-`0` term with the extension of scalars of the sheaf of
relative differentials carries the unit image of the universal differential of `p` back to the
local section `1 ⊗ dp`. -/
lemma tensorDifferentialsIso_inv_unit_universalDerivation (U : Cᵒᵖ)
    (p : (freeAlgebraSheaf J A (underlyingPresheaf J B)).obj.obj U) :
    (tensorDifferentialsIso.{vv, uu, max uu vv ww, max uu vv ww} J A
          (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
          (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
          (canonicalPresentation J A B a)).inv.val.app U
        (((_root_.SheafOfModules.pullbackPushforwardAdjunction
            (Stacks.Sites.Conormal.underlyingRingHomForPullback J
              (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
              (canonicalPresentation J A B a))).unit.app
          (moduleOfDifferentialsOfSite.{vv, uu, max uu vv ww, max uu vv ww} A
            (freeAlgebraSheaf J A (underlyingPresheaf J B))
            (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B)))).val.app U
        ((universalDerivationOfSite.{vv, uu, max uu vv ww, max uu vv ww} A
          (freeAlgebraSheaf J A (underlyingPresheaf J B))
          (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))).d p)) =
      tensorDifferential.{vv, uu, max uu vv ww, max uu vv ww} J A
        (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
        (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
        (canonicalPresentation J A B a) U p :=
  tensorDifferentialsIso_inv_d J _ _ B _ _ U p

/-- The universal property of the degree-`0` term is the composition of its three constituent
bijections. -/
lemma naiveCotangentZeroDerivationEquiv_apply
    (h : (canonicalConormalSequence.{vv, uu, max uu vv ww, max uu vv ww} J A B a).X₂ ⟶ N) :
    naiveCotangentZeroDerivationEquiv.{uu, vv, ww} J A B a N h =
      zeroDerivationStep₃ J A B a N (zeroDerivationStep₂ J A B a N
        (zeroDerivationStep₁ J A B a N h)) :=
  rfl

/-- The first step of the universal property of the degree-`0` term is precomposition with the
comparison of that term with the extension of scalars of the sheaf of relative
differentials. -/
lemma zeroDerivationStep₁_apply
    (h : (canonicalConormalSequence.{vv, uu, max uu vv ww, max uu vv ww} J A B a).X₂ ⟶ N) :
    zeroDerivationStep₁ J A B a N h =
      (tensorDifferentialsIso.{vv, uu, max uu vv ww, max uu vv ww} J A
        (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
        (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
        (canonicalPresentation J A B a)).inv ≫ h :=
  rfl

/-- The first step of the universal property of the degree-`0` term, read on sections. -/
lemma zeroDerivationStep₁_app
    (h : (canonicalConormalSequence.{vv, uu, max uu vv ww, max uu vv ww} J A B a).X₂ ⟶ N)
    (U : Cᵒᵖ)
    (z : ((_root_.SheafOfModules.pullback
        (Stacks.Sites.Conormal.underlyingRingHomForPullback J
          (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
          (canonicalPresentation J A B a))).obj
      (moduleOfDifferentialsOfSite.{vv, uu, max uu vv ww, max uu vv ww} A
        (freeAlgebraSheaf J A (underlyingPresheaf J B))
        (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B)))).val.obj U) :
    (zeroDerivationStep₁ J A B a N h).val.app U z =
      h.val.app U ((tensorDifferentialsIso.{vv, uu, max uu vv ww, max uu vv ww} J A
        (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
        (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
        (canonicalPresentation J A B a)).inv.val.app U z) :=
  rfl

/-- **The derivation attached to a morphism out of the degree-`0` term of the naive cotangent
complex is evaluation at the local sections `1 ⊗ dp`.** This is the universal property of
`B ⊗_{A[B]} Ω_{A[B]/A}` read on sections. -/
lemma naiveCotangentZeroDerivationEquiv_d
    (h : (canonicalConormalSequence.{vv, uu, max uu vv ww, max uu vv ww} J A B a).X₂ ⟶ N)
    (U : Cᵒᵖ) (p : (freeAlgebraSheaf J A (underlyingPresheaf J B)).obj.obj U) :
    (naiveCotangentZeroDerivationEquiv.{uu, vv, ww} J A B a N h).d p =
      h.val.app U (tensorDifferential.{vv, uu, max uu vv ww, max uu vv ww} J A
        (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
        (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
        (canonicalPresentation J A B a) U p) := by
  rw [naiveCotangentZeroDerivationEquiv_apply,
    ← tensorDifferentialsIso_inv_unit_universalDerivation J A B a U p]
  refine Eq.trans (zeroDerivationStep₃_d J A B a N _ U p) ?_
  refine Eq.trans (zeroDerivationStep₂_app J A B a N _ U _) ?_
  exact zeroDerivationStep₁_app J A B a N h U
    (((_root_.SheafOfModules.pullbackPushforwardAdjunction
      (Stacks.Sites.Conormal.underlyingRingHomForPullback J
        (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
        (canonicalPresentation J A B a))).unit.app
    (moduleOfDifferentialsOfSite.{vv, uu, max uu vv ww, max uu vv ww} A
      (freeAlgebraSheaf J A (underlyingPresheaf J B))
      (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B)))).val.app U
    ((universalDerivationOfSite.{vv, uu, max uu vv ww, max uu vv ww} A
      (freeAlgebraSheaf J A (underlyingPresheaf J B))
      (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))).d p))

/-- The left-hand map of the canonical conormal sequence, with its source read as the conormal
sheaf of the canonical polynomial presentation. This is the one spelling in which it is a
morphism out of the object whose universal property
`Stacks.Sites.Conormal.conormalModuleHomEquivOf` describes. -/
noncomputable abbrev canonicalConormalDifferential :
    conormalModule.{max uu vv ww, vv, uu} J (canonicalPresentation J A B a) ⟶
      (canonicalConormalSequence.{vv, uu, max uu vv ww, max uu vv ww} J A B a).X₂ :=
  (canonicalConormalSequence.{vv, uu, max uu vv ww, max uu vv ww} J A B a).f

omit [J.HasSheafCompose (forget₂ CommRingCat.{max uu vv ww} RingCat.{max uu vv ww})] in
/-- The universal property of the conormal sheaf, read on sections: the restriction of a
morphism out of the conormal sheaf to the kernel ideal is its value on conormal classes. -/
lemma conormalModuleHomEquivOf_app
    (G : _root_.SheafOfModules.{max uu vv ww} (Stacks.SheafOfModules.Tensor.ringSheaf B))
    (h : conormalModule.{max uu vv ww, vv, uu} J (canonicalPresentation J A B a) ⟶ G)
    (U : Cᵒᵖ)
    (g : ((idealSheaf.{max uu vv ww, vv, uu} J
      (presentationRingHom.{max uu vv ww, vv, uu} J (canonicalPresentation J A B a))).val.obj U)) :
    (conormalModuleHomEquivOf.{max uu vv ww, vv, uu} J (canonicalPresentation J A B a)
        (presentationRingHom.{max uu vv ww, vv, uu} J (canonicalPresentation J A B a)) rfl G
        h).val.app U g =
      h.val.app U (conormalClass.{vv, uu, max uu vv ww, max uu vv ww} J A
        (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
        (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
        (canonicalPresentation J A B a) U
        (sectionOfIdealSheaf.{max uu vv ww, vv, uu} J (canonicalPresentation J A B a) U g)) :=
  rfl

/-- **The conormal differential, restricted to the kernel ideal and followed by a morphism out
of the degree-`0` term, is the derivation that morphism represents.** Both send a local section
`g` of the kernel ideal to the image of `1 ⊗ dg`. -/
lemma conormalModuleHomEquivOf_canonicalConormalDifferential_app
    (h : (canonicalConormalSequence.{vv, uu, max uu vv ww, max uu vv ww} J A B a).X₂ ⟶ N)
    (U : Cᵒᵖ)
    (g : ((idealSheaf.{max uu vv ww, vv, uu} J
      (presentationRingHom.{max uu vv ww, vv, uu} J (canonicalPresentation J A B a))).val.obj U)) :
    (conormalModuleHomEquivOf.{max uu vv ww, vv, uu} J (canonicalPresentation J A B a)
        (presentationRingHom.{max uu vv ww, vv, uu} J (canonicalPresentation J A B a)) rfl N
        (canonicalConormalDifferential J A B a ≫ h)).val.app U g =
      (naiveCotangentZeroDerivationEquiv.{uu, vv, ww} J A B a N h).d
        ((sectionOfIdealSheaf.{max uu vv ww, vv, uu} J (canonicalPresentation J A B a) U g) :
          (freeAlgebraSheaf J A (underlyingPresheaf J B)).obj.obj U) := by
  rw [naiveCotangentZeroDerivationEquiv_d,
    ← conormalSequence_f_class.{vv, uu, max uu vv ww, max uu vv ww} J A
      (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
      (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
      (canonicalPresentation J A B a) U
      (sectionOfIdealSheaf.{max uu vv ww, vv, uu} J (canonicalPresentation J A B a) U g)]
  exact conormalModuleHomEquivOf_app J A B a N _ U g

end NaiveCotangentZeroSections

section ComplexPlumbing

universe uu vv ww zz

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.SheafOfModules

variable {C : Type uu} [Category.{vv} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{ww}]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  (A B : Sheaf J CommRingCat.{ww}) (a : A ⟶ B)

omit [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})] in
/-- The naive cotangent complex has no nonzero differential out of degree `0`: it is concentrated
in degrees `-1` and `0` and its differential raises degree. -/
theorem naiveCotangentComplex_d_zero_eq_zero (k : ℤ) :
    (naiveCotangentComplex.{vv, uu, ww, zz} J A B a).d 0 k = 0 := by
  have : HasZeroObject
      (_root_.SheafOfModules.{max ww uu vv zz} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  show (HomologicalComplex.double
    (canonicalConormalSequence.{vv, uu, ww, zz} J A B a).f
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)).d 0 k = 0
  exact HomologicalComplex.double_d_eq_zero₀ _ _ 0 k (by decide)

/-- The degree `-1` term of the naive cotangent complex is the conormal sheaf of the canonical
polynomial presentation, as the comparison isomorphism of the two-term complex. -/
noncomputable def naiveCotangentComplexXNegOneIso :
    (naiveCotangentComplex.{vv, uu, ww, zz} J A B a).X (-1) ≅
      (canonicalConormalSequence.{vv, uu, ww, zz} J A B a).X₁ := by
  letI : HasZeroObject
      (_root_.SheafOfModules.{max ww uu vv zz} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  exact HomologicalComplex.doubleXIso₀ (canonicalConormalSequence.{vv, uu, ww, zz} J A B a).f
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)

/-- The degree `0` term of the naive cotangent complex is the scalar extension of the
differentials of the canonical polynomial presentation, as the comparison isomorphism of the
two-term complex. -/
noncomputable def naiveCotangentComplexXZeroIso :
    (naiveCotangentComplex.{vv, uu, ww, zz} J A B a).X 0 ≅
      (canonicalConormalSequence.{vv, uu, ww, zz} J A B a).X₂ := by
  letI : HasZeroObject
      (_root_.SheafOfModules.{max ww uu vv zz} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  exact HomologicalComplex.doubleXIso₁ (canonicalConormalSequence.{vv, uu, ww, zz} J A B a).f
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)

omit [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})] in
/-- The only nonzero differential of the naive cotangent complex is the left-hand map of the
canonical conormal sequence, read through the two comparison isomorphisms of the two-term
complex. -/
theorem naiveCotangentComplex_d_negOne_zero_iso :
    (naiveCotangentComplex.{vv, uu, ww, zz} J A B a).d (-1) 0 =
      (naiveCotangentComplexXNegOneIso.{uu, vv, ww, zz} J A B a).hom ≫
        (canonicalConormalSequence.{vv, uu, ww, zz} J A B a).f ≫
          (naiveCotangentComplexXZeroIso.{uu, vv, ww, zz} J A B a).inv := by
  have : HasZeroObject
      (_root_.SheafOfModules.{max ww uu vv zz} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  exact HomologicalComplex.double_d (canonicalConormalSequence.{vv, uu, ww, zz} J A B a).f
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)

end ComplexPlumbing

section InverseImageNaiveCotangentComplex

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
  (f : MorphismOfTopoi (Sheaf J (Type (max u v w))) (Sheaf K (Type (max u' v' w'))))
  {A B : Sheaf K CommRingCat.{max u' v' w'}} (a : A ⟶ B)

/-- **The conormal sheaf of the inverse image of the canonical presentation is the conormal
sheaf of the canonical presentation of the inverse image.** The inverse image `f⁻¹(A[B]) ⟶ f⁻¹B`
of the canonical polynomial presentation is a presentation of `f⁻¹B` isomorphic to, but not
equal to, the canonical presentation `(f⁻¹A)[f⁻¹B] ⟶ f⁻¹B`, and this is the transport of the
conormal sheaf along `Stacks.Sites.FreeAlgebra.inverseImageFreeAlgebraIso`. -/
noncomputable def inverseImagePresentationConormalIso :
    conormalModule.{max u v w, v, u} J
        (f.inverseImageRing.map (canonicalPresentation K A B a)) ≅
      (canonicalConormalSequence.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A)
        (f.inverseImageRing.obj B) (f.inverseImageRing.map a)).X₁ :=
  conormalModuleIsoOfFac.{max u v w, v, u} J (f.inverseImageRing.map
      (canonicalPresentation K A B a))
    (canonicalPresentation J (f.inverseImageRing.obj A) (f.inverseImageRing.obj B)
      (f.inverseImageRing.map a))
    (inverseImageFreeAlgebraIso f A B)
    (inverseImageFreeAlgebraHom_comp_canonicalPresentation f A B a)

/-- **The inverse image of the degree `-1` term of the naive cotangent complex is the degree
`-1` term of the naive cotangent complex of the inverse image**: the identification
`f⁻¹(I/I²) ≅ I'/(I')²` of the conormal sheaves of the canonical polynomial presentations. It is
`Stacks.Sheaves.RingedToposModules.inverseImageConormalIso` at the inverse image of the
canonical presentation, followed by the transport along the identification
`f⁻¹(A[B]) ≅ (f⁻¹A)[f⁻¹B]` of the two presentations of `f⁻¹B`. -/
noncomputable def inverseImageNaiveCotangentNegOneIso :
    (inverseImageTargetModules.{u, v, w, u', v', w'} J K f (B := B)).obj
        (canonicalConormalSequence.{v', u', max u' v' w', max u' v' w'} K A B a).X₁ ≅
      (canonicalConormalSequence.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A)
        (f.inverseImageRing.obj B) (f.inverseImageRing.map a)).X₁ :=
  (inverseImageConormalIso.{max u v w, max u' v' w', v, u, v', u'} f
      (canonicalPresentation K A B a)).trans
    (inverseImagePresentationConormalIso J K f a)

omit [HasWeakSheafify J CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u' v' w'} RingCat.{max u' v' w'})] in
/-- The identification of the morphisms out of the two conormal sheaves is precomposition with
the backward morphism of the isomorphism it produces. -/
lemma inverseImageConormalHomEquiv_apply
    (M : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B)))
    (x : (inverseImageTargetModules.{u, v, w, u', v', w'} J K f (B := B)).obj
        (conormalModule.{max u' v' w', v', u'} K (canonicalPresentation K A B a)) ⟶ M) :
    inverseImageConormalHomEquiv.{max u v w, max u' v' w', v, u, v', u'} f
        (canonicalPresentation K A B a) M x =
      (inverseImageConormalIso.{max u v w, max u' v' w', v, u, v', u'} f
        (canonicalPresentation K A B a)).inv ≫ x :=
  isoOfNaturalHomEquiv_apply _ (naturalHomEquiv_inverseImageConormalHomEquiv f
    (canonicalPresentation K A B a)) M x

/-- The degree-`0` comparison is the Yoneda transport of the identity along the bijection of
Stacks 08TZ on the degree-`0` terms. -/
lemma inverseImageNaiveCotangentZeroIso_hom :
    (inverseImageNaiveCotangentZeroIso J K f a).hom =
      (inverseImageNaiveCotangentZeroHomEquiv J K f a
        (canonicalConormalSequence.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A)
          (f.inverseImageRing.obj B) (f.inverseImageRing.map a)).X₂).symm (𝟙 _) :=
  isoOfNaturalHomEquiv_hom (inverseImageNaiveCotangentZeroHomEquiv J K f a)
    (naturalHomEquiv_inverseImageNaiveCotangentZeroHomEquiv J K f a)

/-- The bijection of Stacks 08TZ on the degree-`0` terms is the universal property of the
inverse image followed by the inverse of the universal property of the degree-`0` term of the
inverse image, read backwards. -/
lemma inverseImageNaiveCotangentZeroHomEquiv_symm_apply
    (M : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B)))
    (y : (canonicalConormalSequence.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A)
      (f.inverseImageRing.obj B) (f.inverseImageRing.map a)).X₂ ⟶ M) :
    (inverseImageNaiveCotangentZeroHomEquiv J K f a M).symm y =
      (inverseImageNaiveCotangentZeroDerivationEquiv J K f a M).symm
        (naiveCotangentZeroDerivationEquiv.{u, v, w} J (f.inverseImageRing.obj A)
          (f.inverseImageRing.obj B) (f.inverseImageRing.map a) M y) :=
  rfl

/-- **The degree-`0` comparison of Stacks 08TZ is the morphism whose attached
`f⁻¹A`-derivation of `(f⁻¹A)[f⁻¹B]` is the universal one.** This is the characterisation of
that comparison by the universal property it was built from. -/
theorem inverseImageNaiveCotangentZeroIso_derivation :
    inverseImageNaiveCotangentZeroDerivationEquiv J K f a
        (canonicalConormalSequence.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A)
          (f.inverseImageRing.obj B) (f.inverseImageRing.map a)).X₂
        (inverseImageNaiveCotangentZeroIso J K f a).hom =
      naiveCotangentZeroDerivationEquiv.{u, v, w} J (f.inverseImageRing.obj A)
        (f.inverseImageRing.obj B) (f.inverseImageRing.map a) _ (𝟙 _) := by
  rw [inverseImageNaiveCotangentZeroIso_hom, inverseImageNaiveCotangentZeroHomEquiv_symm_apply,
    Equiv.apply_symm_apply]

omit [HasWeakSheafify J CommRingCat.{max u v w}] in
/-- The transport of a derivation along the equality of the two spellings of the inverse-image
ring map does not change its values on local sections. This is the fifth of the six bijections
composing the universal property of the inverse image of the degree-`0` term. -/
lemma inverseImageZeroStep₅_d
    (M : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B)))
    (DD : ((show _root_.SheafOfModules.{max u v w} (Tensor.ringSheaf.{u, v, max u v w}
            (f.inverseImageRing.obj (freeAlgebraSheaf K A (underlyingPresheaf K B)))) from
          (_root_.SheafOfModules.restrictScalars (inverseImageRingMap f
            (underlyingRingHomOfSite (canonicalPresentation K A B a)))).obj M)).val.Derivation'
        (f.inverseImageRing.map
          (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B))).hom)
    {U : Cᵒᵖ}
    (z : (f.inverseImageRing.obj
      (freeAlgebraSheaf K A (underlyingPresheaf K B))).obj.obj U) :
    (inverseImageZeroStep₅ J K f a M DD).d z = DD.d z := by
  unfold inverseImageZeroStep₅
  exact restrictScalarsDerivationCongr_d
    (P := f.inverseImageRing.obj (freeAlgebraSheaf K A (underlyingPresheaf K B)))
    (R := Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj B)) M
    (forgetCommRingSheaf_map_pullbackCommRingSheafMap J f.inverseImage
      (canonicalPresentation K A B a)).symm
    (f.inverseImageRing.map (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B)))
    DD z

omit [K.HasSheafCompose (forget₂ CommRingCat.{max u' v' w'} RingCat.{max u' v' w'})] in
/-- The transport of a derivation along the identification `f⁻¹(A[B]) ≅ (f⁻¹A)[f⁻¹B]` of the two
presentations of `f⁻¹B` evaluates at a local section of `(f⁻¹A)[f⁻¹B]` by carrying it back to
`f⁻¹(A[B])`. This is the sixth of the six bijections composing the universal property of the
inverse image of the degree-`0` term. -/
lemma inverseImageZeroStep₆_d
    (M : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B)))
    (DD : (((_root_.SheafOfModules.restrictScalars
        ((Stacks.forgetCommRingSheaf.{v, u, max u v w} J).map
          (f.inverseImageRing.map (canonicalPresentation K A B a)))).obj M).val).Derivation'
        (f.inverseImageRing.map
          (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B))).hom)
    {U : Cᵒᵖ}
    (z : (freeAlgebraSheaf J (f.inverseImageRing.obj A)
      (underlyingPresheaf J (f.inverseImageRing.obj B))).obj.obj U) :
    (inverseImageZeroStep₆ J K f a M DD).d z =
      DD.d ((inverseImageFreeAlgebraIso f A B).inv.hom.app U z) :=
  rfl

/-- **The `f⁻¹A`-derivation of `(f⁻¹A)[f⁻¹B]` attached to a morphism out of the inverse image of
the degree-`0` term, evaluated at the image of a local section of `f⁻¹(A[B])`.** The last two
of the six bijections composing the universal property of that inverse image are transports
which do not change the values of the derivation, so the value is that of the derivation
produced by the first four bijections. -/
lemma inverseImageNaiveCotangentZeroDerivationEquiv_d_freeAlgebraIso
    (M : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B)))
    (h : (inverseImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'} B)).obj
        (canonicalConormalSequence.{v', u', max u' v' w', max u' v' w'} K A B a).X₂ ⟶ M)
    (U : Cᵒᵖ)
    (z : (f.inverseImageRing.obj
      (freeAlgebraSheaf K A (underlyingPresheaf K B))).obj.obj U) :
    (inverseImageNaiveCotangentZeroDerivationEquiv J K f a M h).d
        ((inverseImageFreeAlgebraIso f A B).hom.hom.app U z) =
      (inverseImageZeroStep₄ J K f a M (inverseImageZeroStep₃ J K f a M
        (pushforwardZeroDerivation J K f a M h))).d z := by
  have hinv : (inverseImageFreeAlgebraIso f A B).inv.hom.app U
      ((inverseImageFreeAlgebraIso f A B).hom.hom.app U z) = z :=
    congrArg (fun k : f.inverseImageRing.obj
        (freeAlgebraSheaf K A (underlyingPresheaf K B)) ⟶
          f.inverseImageRing.obj (freeAlgebraSheaf K A (underlyingPresheaf K B)) ↦
      k.hom.app U z) (inverseImageFreeAlgebraIso f A B).hom_inv_id
  rw [inverseImageNaiveCotangentZeroDerivationEquiv_apply, inverseImageZeroStep₆_d, hinv,
    inverseImageZeroStep₅_d]

/-- The isomorphism of the degree `0` terms of Stacks 08TZ, with the inverse image of sheaves
of modules read as a functor into the modules over the sheaf of rings underlying `f⁻¹B`. This is
the one spelling of the coefficient ring sheaf in which the two terms of the naive cotangent
complex and the inverse image of the two terms of the naive cotangent complex of `a` are
modules over the very same sheaf of rings. -/
noncomputable def inverseImageNaiveCotangentZeroTargetIso :
    (inverseImageTargetModules.{u, v, w, u', v', w'} J K f (B := B)).obj
        (canonicalConormalSequence.{v', u', max u' v' w', max u' v' w'} K A B a).X₂ ≅
      (canonicalConormalSequence.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A)
        (f.inverseImageRing.obj B) (f.inverseImageRing.map a)).X₂ :=
  inverseImageNaiveCotangentZeroIso J K f a

/-- The square expressing that the two comparisons of the terms of the naive cotangent complex
commute with the two conormal differentials, in the orientation in which it becomes the
commutation hypothesis of `HomologicalComplex.homFromMapDouble`. -/
abbrev InverseImageNaiveCotangentSquare : Prop :=
  (inverseImageNaiveCotangentNegOneIso J K f a).hom ≫
      (canonicalConormalSequence.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A)
        (f.inverseImageRing.obj B) (f.inverseImageRing.map a)).f =
    (inverseImageTargetModules.{u, v, w, u', v', w'} J K f (B := B)).map
        (canonicalConormalSequence.{v', u', max u' v' w', max u' v' w'} K A B a).f ≫
      (inverseImageNaiveCotangentZeroTargetIso J K f a).hom

end InverseImageNaiveCotangentComplex

end Stacks.SheafOfModules

end
