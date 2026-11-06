module

public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentInverseImageComplex
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentSquare

/-!
# Naturality of the inverse image of the naive cotangent complex in the base ring

Let `f : Sh(C) ⟶ Sh(D)` be a morphism of topoi and `a = φ ≫ a'` a factorisation of a homomorphism
`a : A ⟶ B` of sheaves of commutative rings on `D` through `a' : A' ⟶ B`. The change of base
ring `NL_{B/A} ⟶ NL_{B/A'}` of Stacks 08TX and the identification `f⁻¹ NL_{B/A} ≅ NL_{f⁻¹B/f⁻¹A}`
of Stacks 08TZ commute. This file proves it in degree `0`, where the comparison of Stacks 08TZ
is characterised by the derivations it represents.

## Main results

* `Stacks.SheafOfModules.freeAlgebraSheafDerivation_ext_of_variable`: a derivation of a free
  algebra sheaf is determined by its values on the variables.
* `Stacks.SheafOfModules.inverseImageNaiveCotangentZeroDerivationEquiv_d_variable_naturality`:
  the derivation attached to a morphism out of `f⁻¹(B ⊗_{A[B]} Ω_{A[B]/A})` is natural in the
  base ring, on the variables.
* `Stacks.SheafOfModules.inverseImageNaiveCotangentZeroTargetIso_naturality`: **Stacks 08TZ is
  natural in the base ring, in degree `0`.**

## Implementation notes

The comparison of Stacks 08TZ in degree `0` passes through the exchange
`Stacks.Sheaves.RingedToposModules.directImageModulesRestrictScalarsIso` of the direct image with
restriction of scalars, which depends on the presentation. Two such exchanges for the two
presentations `A[B] ⟶ B` and `A'[B] ⟶ B` are never compared on local sections: the elaborator
accepts such a statement but the kernel times out on the carriers. Instead the exchange is
removed once and for all at the level of morphisms of sheaves of sets
(`homEquiv_symm_comp_moduleSheafFunctor_map_directImageModulesRestrictScalarsIso`), where it is a
transport along identities of underlying sheaves of sets, and the values at the variables are
collected into one morphism `pushforwardZeroVariableHom` whose declared target is common to both
presentations.

## References

* [Stacks Project, Tag 08TZ](https://stacks.math.columbia.edu/tag/08TZ)
* [Stacks Project, Tag 08TX](https://stacks.math.columbia.edu/tag/08TX)
-/

@[expose] public noncomputable section

namespace Stacks.Sheaves.RingedToposModules

section DirectImageRestrictScalarsTranspose

open CategoryTheory Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback

universe w w' v u v' u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  {O O' : Sheaf K RingCat.{w'}} (c : O' ⟶ O)
  (M : SheafOfModules.{w} (inverseImageRingSheaf f O))

/-- The underlying sheaf of sets of the restriction of scalars along `c` of the direct image of
`M`, written as the direct image of the underlying sheaf of sets of `M`. -/
lemma moduleSheaf_restrictScalars_directImageModules :
    Sheaf.moduleSheaf O' ((SheafOfModules.restrictScalars c).obj ((directImageModules f O).obj M)) =
      f.pushforward.obj (Sheaf.moduleSheaf (inverseImageRingSheaf f O) M) := rfl

/-- **The comparison of the direct image with restriction of scalars, transposed.** For a
morphism of sheaves of sets `g` into the underlying sheaf of sets of the restriction of scalars
of a direct image, the transpose across `f⁻¹ ⊣ f_*` of `g` followed by the comparison is the
transpose of `g` itself, read through the identity of underlying sheaves of sets. -/
lemma homEquiv_symm_comp_moduleSheafFunctor_map_directImageModulesRestrictScalarsIso
    {X : Sheaf K (Type w')}
    (g : X ⟶ Sheaf.moduleSheaf O' ((SheafOfModules.restrictScalars c).obj
      ((directImageModules f O).obj M))) :
    (f.adj.homEquiv _ _).symm (g ≫ (Sheaf.moduleSheafFunctor O').map
        (directImageModulesRestrictScalarsIso f c M).hom) =
      (f.adj.homEquiv _ _).symm
          (g ≫ eqToHom (moduleSheaf_restrictScalars_directImageModules f c M)) ≫
        eqToHom (moduleSheaf_restrictScalars (inverseImageRingMap f c) M).symm := by
  have e : eqToHom (moduleSheaf_directImageModules_restrictScalars f c M) =
      eqToHom (moduleSheaf_restrictScalars_directImageModules f c M) ≫
        f.pushforward.map
          (eqToHom (moduleSheaf_restrictScalars (inverseImageRingMap f c) M).symm) := by
    rw [eqToHom_map, eqToHom_trans]
    rfl
  rw [moduleSheafFunctor_map_directImageModulesRestrictScalarsIso_hom, e, ← Category.assoc,
    Adjunction.homEquiv_naturality_right_symm]

/-- Two local sections of the restrictions of scalars of a direct image along two ring maps, equal
as local sections, have equal images in the direct image of the underlying sheaf of sets. -/
lemma sectionsFunctor_map_eqToHom_moduleSheaf_restrictScalars_directImageModules_congr
    {O₁ O₂ : Sheaf K RingCat.{w'}} (c₁ : O₁ ⟶ O) (c₂ : O₂ ⟶ O) (V : Dᵒᵖ)
    (y₁ : (Sheaf.sectionsFunctor K V).obj (Sheaf.moduleSheaf O₁
      ((SheafOfModules.restrictScalars c₁).obj ((directImageModules f O).obj M))))
    (y₂ : (Sheaf.sectionsFunctor K V).obj (Sheaf.moduleSheaf O₂
      ((SheafOfModules.restrictScalars c₂).obj ((directImageModules f O).obj M))))
    (h : @Eq ↥(((SheafOfModules.restrictScalars c₁).obj ((directImageModules f O).obj M)).val.obj V)
      y₁ y₂) :
    (Sheaf.sectionsFunctor K V).map
        (eqToHom (moduleSheaf_restrictScalars_directImageModules f c₁ M)) y₁ =
      (Sheaf.sectionsFunctor K V).map
        (eqToHom (moduleSheaf_restrictScalars_directImageModules f c₂ M)) y₂ :=
  h

/-- The comparison of the direct image with restriction of scalars is the identity on local
sections of the underlying sheaves of sets. -/
lemma sectionsFunctor_map_eqToHom_moduleSheaf_directImageModules_restrictScalars (V : Dᵒᵖ)
    (y : (Sheaf.sectionsFunctor K V).obj (Sheaf.moduleSheaf O'
      ((SheafOfModules.restrictScalars c).obj ((directImageModules f O).obj M)))) :
    (Sheaf.sectionsFunctor K V).map
      (eqToHom (moduleSheaf_directImageModules_restrictScalars f c M)) y = y := by
  have h1 := moduleSheaf_restrictScalars c ((directImageModules f O).obj M)
  have h12 : Sheaf.moduleSheaf O ((directImageModules f O).obj M) =
      Sheaf.moduleSheaf O ((SheafOfModules.restrictScalars (ringUnit f O)).obj
        ((pushforwardModuleFunctor f (inverseImageRingSheaf f O)).obj M)) := rfl
  have h2 := moduleSheaf_restrictScalars (ringUnit f O)
    ((pushforwardModuleFunctor f (inverseImageRingSheaf f O)).obj M)
  have h3 := moduleSheaf_restrictScalars (ringUnit f O')
    ((pushforwardModuleFunctor f (inverseImageRingSheaf f O')).obj
        ((SheafOfModules.restrictScalars (inverseImageRingMap f c)).obj M))
  have h4 := moduleSheaf_pullbackModuleObj_restrictScalars K f.pushforward
    (inverseImageRingMap f c) M
  have h5 : Sheaf.moduleSheaf (pushforwardRingSheaf f (inverseImageRingSheaf f O))
        ((pushforwardModuleFunctor f (inverseImageRingSheaf f O)).obj M) =
      Sheaf.moduleSheaf (pullbackRingSheaf K f.pushforward (inverseImageRingSheaf f O))
        (pullbackModuleObj K f.pushforward (inverseImageRingSheaf f O) M) := rfl
  have h6 : Sheaf.moduleSheaf (pullbackRingSheaf K f.pushforward (inverseImageRingSheaf f O'))
        (pullbackModuleObj K f.pushforward (inverseImageRingSheaf f O')
          ((SheafOfModules.restrictScalars (inverseImageRingMap f c)).obj M)) =
      Sheaf.moduleSheaf (pushforwardRingSheaf f (inverseImageRingSheaf f O'))
        ((pushforwardModuleFunctor f (inverseImageRingSheaf f O')).obj
          ((SheafOfModules.restrictScalars (inverseImageRingMap f c)).obj M)) := rfl
  have h7 : Sheaf.moduleSheaf O' ((SheafOfModules.restrictScalars (ringUnit f O')).obj
        ((pushforwardModuleFunctor f (inverseImageRingSheaf f O')).obj
          ((SheafOfModules.restrictScalars (inverseImageRingMap f c)).obj M))) =
      Sheaf.moduleSheaf O' ((directImageModules f O').obj
        ((SheafOfModules.restrictScalars (inverseImageRingMap f c)).obj M)) := rfl
  have hsplit : eqToHom (moduleSheaf_directImageModules_restrictScalars f c M) =
      eqToHom h1 ≫ eqToHom h12 ≫ eqToHom h2 ≫ eqToHom h5 ≫ eqToHom h4.symm ≫ eqToHom h6 ≫
        eqToHom h3.symm ≫ eqToHom h7 := by
    simp only [eqToHom_trans]
  rw [hsplit, Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp,
    Functor.map_comp, Functor.map_comp, Functor.map_comp]
  rfl

/-- The underlying sheaf of sets of a direct image is the direct image of the underlying sheaf of
sets. -/
lemma moduleSheaf_directImageModules (F : SheafOfModules.{w} (inverseImageRingSheaf f O)) :
    Sheaf.moduleSheaf O ((directImageModules f O).obj F) =
      f.pushforward.obj (Sheaf.moduleSheaf (inverseImageRingSheaf f O) F) := rfl

/-- The transpose across Stacks 03D3 of a morphism out of an inverse image is, on underlying
sheaves of sets, the transpose of its underlying morphism of sheaves of sets, read through the
identification of the underlying sheaf of sets of a direct image. -/
lemma moduleSheafFunctor_map_toposModulesHomEquiv_comp_eqToHom
    {G : SheafOfModules.{w'} O} {F : SheafOfModules.{w} (inverseImageRingSheaf f O)}
    (x : (inverseImageModules f O).obj G ⟶ F) :
    (Sheaf.moduleSheafFunctor O).map (toposModulesHomEquiv f O G F x) ≫
        eqToHom (moduleSheaf_directImageModules f F) =
      f.adj.homEquiv _ _ ((Sheaf.moduleSheafFunctor (inverseImageRingSheaf f O)).map x) :=
  rfl

omit [K.HasSheafCompose (forget RingCat)] in
/-- Restriction of scalars acts on a morphism of sheaves of modules by the same morphism of
underlying sheaves of sets, read through the two identifications of underlying sheaves of
sets. -/
lemma moduleSheafFunctor_map_restrictScalars_map_eq_eqToHom
    {R R' : Sheaf K RingCat.{w'}} (a : R ⟶ R') {N N' : SheafOfModules.{w'} R'} (y : N ⟶ N') :
    (Sheaf.moduleSheafFunctor R).map ((SheafOfModules.restrictScalars a).map y) =
      eqToHom (moduleSheaf_restrictScalars a N) ≫ (Sheaf.moduleSheafFunctor R').map y ≫
        eqToHom (moduleSheaf_restrictScalars a N').symm :=
  rfl

end DirectImageRestrictScalarsTranspose

end Stacks.Sheaves.RingedToposModules

namespace Stacks.Sheaves.RingedToposModules

section ConormalClassChar

universe w w' v u v' u'

open CategoryTheory Stacks.Sites.Conormal

attribute [local implicit_reducible] CategoryTheory.sheafCompose

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{max u' v' w'})]
  (f : MorphismOfTopoi (Sheaf J (Type (max u v w))) (Sheaf K (Type (max u' v' w'))))
  {A B : Sheaf K CommRingCat.{max u' v' w'}} (φ : A ⟶ B) [Presheaf.IsLocallySurjective K φ.hom]

/-- The class map `ℐ ⟶ ℐ/ℐ²` of a presentation `φ : 𝒜 ⟶ ℬ`, as a morphism of sheaves of
`𝒜`-modules. -/
noncomputable abbrev conormalClassHom :
    idealSheaf.{w', v', u'} K (presentationRingHom.{w', v', u'} K φ) ⟶
      (SheafOfModules.restrictScalars (presentationRingHom.{w', v', u'} K φ)).obj
        (conormalModule.{w', v', u'} K φ) :=
  conormalModuleHomEquivOf.{w', v', u'} K φ
    (presentationRingHom.{w', v', u'} K φ) rfl _ (𝟙 _)

/-- The class map `ℐ' ⟶ ℐ'/ℐ'²` of the inverse image `f⁻¹φ` of a presentation, as a morphism of
sheaves of `f⁻¹𝒜`-modules. -/
noncomputable abbrev inverseImageConormalClassHom :
    idealSheaf.{w, v, u} J (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ) ⟶
      (SheafOfModules.restrictScalars
        (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).obj
        (conormalModule.{w, v, u} J (f.inverseImageRing.map φ)) :=
  conormalModuleHomEquivOf.{w, v, u} J (f.inverseImageRing.map φ)
    (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)
    (inverseImageRingMap_presentationRingHom.{w, w', v, u, v', u'} f φ) _ (𝟙 _)

/-- **The six-step identification sends the comparison of Stacks 08TZ to the class map.** -/
lemma conormalInverseImageIdealSheafEquiv_inverseImageConormalIso_hom :
    conormalInverseImageIdealSheafEquiv f φ
        (conormalModule.{w, v, u} J (f.inverseImageRing.map φ))
        (inverseImageConormalIso f φ).hom =
      inverseImageConormalClassHom f φ := by
  have h : inverseImageConormalHomEquiv f φ
      (conormalModule.{w, v, u} J (f.inverseImageRing.map φ))
      (inverseImageConormalIso f φ).hom = 𝟙 _ := by
    rw [inverseImageConormalIso, isoOfNaturalHomEquiv_hom, Equiv.apply_symm_apply]
  rw [inverseImageConormalHomEquiv, Equiv.trans_apply] at h
  exact (Equiv.symm_apply_eq _).1 h

/-- The identification `f⁻¹ℐ ≅ ℐ'` followed by the class map of `f⁻¹φ` is the transpose of the
identification of the restriction to `ℐ` of the transpose of the comparison of Stacks 08TZ. -/
lemma inverseImageIdealIso_hom_comp_inverseImageConormalClassHom :
    (inverseImageIdealIso.{w, w', v, u, v', u'} f φ).hom ≫ inverseImageConormalClassHom f φ =
      inverseImageIdealAdjunctionEquiv f φ _
        (conormalIdealDirectImageRestrictEquiv f φ _ (conormalDirectImageIdealEquiv f φ _
          (conormalInverseImageAdjunctionEquiv f φ _ (inverseImageConormalIso f φ).hom))) := by
  rw [← conormalInverseImageIdealSheafEquiv_inverseImageConormalIso_hom]
  show (inverseImageIdealIso.{w, w', v, u, v', u'} f φ).hom ≫
    (inverseImageIdealIso.{w, w', v, u, v', u'} f φ).inv ≫ _ = _
  rw [Iso.hom_inv_id_assoc]
  rfl

/-- The transpose across Stacks 03D3 of a morphism out of an inverse image is, on underlying
sheaves of sets, the transpose of its underlying morphism of sheaves of sets, read through the
identification of the underlying sheaf of sets of a direct image. -/
lemma moduleSheafFunctor_map_commModulesAdjunction_homEquiv_comp_eqToHom
    (G : SheafOfModules.{max u' v' w'} (SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} B))
    (F : SheafOfModules.{max u v w}
      (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj B)))
    (x : (inverseImageCommModules.{w, w', v, u, v', u'} f B).obj G ⟶ F) :
    (Sheaf.moduleSheafFunctor (SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} B)).map
        ((commModulesAdjunction.{w, w', v, u, v', u'} f B).homEquiv G F x) ≫
        eqToHom (moduleSheaf_directImageModules f F) =
      f.adj.homEquiv _ _
        ((Sheaf.moduleSheafFunctor
          (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w}
            (f.inverseImageRing.obj B))).map x) := by
  rw [show (commModulesAdjunction.{w, w', v, u, v', u'} f B).homEquiv =
      toposModulesHomEquiv f (SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} B) from
    Adjunction.mkOfHomEquiv_homEquiv _]
  exact moduleSheafFunctor_map_toposModulesHomEquiv_comp_eqToHom f x

omit [K.HasSheafCompose (forget AddCommGrpCat)] in
/-- The restriction of a morphism out of the conormal sheaf to the kernel ideal is the class map
followed by that morphism. -/
lemma conormalModuleHomEquivOf_eq_conormalClassHom_comp
    (G : SheafOfModules.{max u' v' w'} (SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} B))
    (y : conormalModule.{w', v', u'} K φ ⟶ G) :
    conormalModuleHomEquivOf.{w', v', u'} K φ
        (presentationRingHom.{w', v', u'} K φ) rfl G y =
      conormalClassHom φ ≫
        (SheafOfModules.restrictScalars (presentationRingHom.{w', v', u'} K φ)).map y := by
  have h := conormalModuleHomEquivOf_comp.{w', v', u'} K φ
    (presentationRingHom.{w', v', u'} K φ) rfl _ G (𝟙 _) y
  rw [Category.id_comp] at h
  exact h

/-- On underlying sheaves of sets, the morphism out of the kernel ideal attached to a morphism `x`
of the conormal sheaf into a direct image is the class map followed by `x`, read through the
identifications of underlying sheaves of sets. -/
lemma moduleSheafFunctor_map_conormalIdealDirectImageRestrictEquiv
    (M : SheafOfModules.{max u v w}
      (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj B)))
    (x : conormalModule.{w', v', u'} K φ ⟶
      (directImageCommModules.{w, w', v, u, v', u'} f B).obj M) :
    (Sheaf.moduleSheafFunctor (SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} A)).map
        (conormalIdealDirectImageRestrictEquiv f φ M (conormalDirectImageIdealEquiv f φ M x)) =
      (Sheaf.moduleSheafFunctor (SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} A)).map
          (conormalClassHom φ) ≫
        eqToHom (moduleSheaf_restrictScalars (presentationRingHom.{w', v', u'} K φ)
          (conormalModule.{w', v', u'} K φ)) ≫
        (Sheaf.moduleSheafFunctor
          (SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} B)).map x ≫
        eqToHom (moduleSheaf_restrictScalars (presentationRingHom.{w', v', u'} K φ)
          ((directImageCommModules.{w, w', v, u, v', u'} f B).obj M)).symm ≫
        eqToHom (moduleSheaf_directImageModules_restrictScalars f
          (presentationRingHom.{w', v', u'} K φ) M) := by
  rw [conormalIdealDirectImageRestrictEquiv_apply, conormalDirectImageIdealEquiv,
    conormalModuleHomEquivOf_eq_conormalClassHom_comp, Functor.map_comp, Functor.map_comp,
    moduleSheafFunctor_map_restrictScalars_map_eq_eqToHom, directImageRestrictScalarsIso]
  exact (congrArg (fun t =>
    ((Sheaf.moduleSheafFunctor (SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} A)).map
          (conormalClassHom φ) ≫
        eqToHom (moduleSheaf_restrictScalars (presentationRingHom.{w', v', u'} K φ)
          (conormalModule.{w', v', u'} K φ)) ≫
        (Sheaf.moduleSheafFunctor
          (SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} B)).map x ≫
        eqToHom (moduleSheaf_restrictScalars (presentationRingHom.{w', v', u'} K φ)
          ((directImageCommModules.{w, w', v, u, v', u'} f B).obj M)).symm) ≫ t)
    (moduleSheafFunctor_map_directImageModulesRestrictScalarsIso_hom f
      (presentationRingHom.{w', v', u'} K φ) M)).trans (by simp only [Category.assoc])

/-- **The comparison of Stacks 08TZ on conormal sheaves, characterised on classes**, transposed
across `f⁻¹ ⊣ f_*` and read on underlying sheaves of sets: the class map of `φ` followed by the
transpose of the comparison is the transpose of the identification `f⁻¹ℐ ≅ ℐ'` followed by the
class map of `f⁻¹φ`. -/
lemma homEquiv_inverseImageIdealIso_hom_comp_inverseImageConormalClassHom :
    f.adj.homEquiv
        ((Sheaf.moduleSheafFunctor (SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} A)).obj
          (idealSheaf.{w', v', u'} K (presentationRingHom.{w', v', u'} K φ)))
        ((Sheaf.moduleSheafFunctor
            (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj A))).obj
          ((SheafOfModules.restrictScalars
            (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).obj
            (conormalModule.{w, v, u} J (f.inverseImageRing.map φ))))
        ((Sheaf.moduleSheafFunctor
            (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj A))).map
          ((inverseImageIdealIso.{w, w', v, u, v', u'} f φ).hom ≫
            inverseImageConormalClassHom f φ)) ≫
        f.pushforward.map (eqToHom (moduleSheaf_restrictScalars
          (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)
          (conormalModule.{w, v, u} J (f.inverseImageRing.map φ)))) =
      (Sheaf.moduleSheafFunctor (SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} A)).map
          (conormalClassHom φ) ≫
        eqToHom (moduleSheaf_restrictScalars (presentationRingHom.{w', v', u'} K φ)
          (conormalModule.{w', v', u'} K φ)) ≫
        f.adj.homEquiv
          ((Sheaf.moduleSheafFunctor (SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} B)).obj
            (conormalModule.{w', v', u'} K φ))
          ((Sheaf.moduleSheafFunctor
              (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj B))).obj
            (conormalModule.{w, v, u} J (f.inverseImageRing.map φ)))
          ((Sheaf.moduleSheafFunctor
              (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj B))).map
            (inverseImageConormalIso f φ).hom) := by
  have h1 : f.adj.homEquiv
        ((Sheaf.moduleSheafFunctor (SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} A)).obj
          (idealSheaf.{w', v', u'} K (presentationRingHom.{w', v', u'} K φ)))
        ((Sheaf.moduleSheafFunctor
            (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj A))).obj
          ((SheafOfModules.restrictScalars
            (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).obj
            (conormalModule.{w, v, u} J (f.inverseImageRing.map φ))))
        ((Sheaf.moduleSheafFunctor
            (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj A))).map
          ((inverseImageIdealIso.{w, w', v, u, v', u'} f φ).hom ≫
            inverseImageConormalClassHom f φ)) =
      (Sheaf.moduleSheafFunctor (SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} A)).map
          (conormalIdealDirectImageRestrictEquiv f φ _ (conormalDirectImageIdealEquiv f φ _
            (conormalInverseImageAdjunctionEquiv.{w, w', v, u, v', u'} f φ
              (conormalModule.{w, v, u} J (f.inverseImageRing.map φ))
              (inverseImageConormalIso f φ).hom))) ≫
        eqToHom rfl := by
    have step := congrArg (Sheaf.moduleSheafFunctor
      (SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj A))).map
      (inverseImageIdealIso_hom_comp_inverseImageConormalClassHom f φ)
    exact ((congrArg _ (step.trans
      (moduleSheafFunctor_map_inverseImageIdealAdjunctionEquiv f A φ _ _))).trans
      (Equiv.apply_symm_apply _ _)).trans (Category.comp_id _).symm
  have h3 := moduleSheafFunctor_map_commModulesAdjunction_homEquiv_comp_eqToHom f
    (conormalModule.{w', v', u'} K φ) (conormalModule.{w, v, u} J (f.inverseImageRing.map φ))
    (inverseImageConormalIso f φ).hom
  rw [h1, moduleSheafFunctor_map_conormalIdealDirectImageRestrictEquiv, ← h3]
  simp only [eqToHom_map, eqToHom_trans]
  rfl

end ConormalClassChar

end Stacks.Sheaves.RingedToposModules

namespace Stacks.SheafOfModules

section VariableDerivation

open CategoryTheory Stacks.Sites.FreeAlgebra Stacks.Sheaves.RingedToposModules

universe w₁ v₁ u₁

variable {D : Type u₁} [Category.{v₁} D] (K : GrothendieckTopology D)
  [HasWeakSheafify K CommRingCat.{w₁}] [K.HasSheafCompose (forget AddCommGrpCat.{w₁})]
  (A B : Sheaf K CommRingCat.{w₁})

/-- The values of a derivation of a free algebra sheaf at the variables, as local sections of the
underlying sheaf of sets. -/
lemma sectionsFunctor_map_variableSheaf_comp_derivationSheafHom
    (N : _root_.SheafOfModules.{w₁}
      (Stacks.SheafOfModules.Tensor.ringSheaf (freeAlgebraSheaf K A (underlyingPresheaf K B))))
    (Dr : PresheafOfModulesOfCommRing.Derivation' N.val
      (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B)).hom)
    (V : Dᵒᵖ) (b : (Sheaf.sectionsFunctor K V).obj
      ((sheafCompose K (forget CommRingCat.{w₁})).obj B)) :
    @Eq ↥(N.val.obj V)
      ((Sheaf.sectionsFunctor K V).map (variableSheaf K A B ≫ derivationSheafHom _ N Dr) b)
      (Dr.d ((freeAlgebraSheafVariable K A (underlyingPresheaf K B)).app V b)) :=
  rfl

end VariableDerivation

open CategoryTheory in
/-- Two transports of a morphism into the underlying sheaf of sets of a sheaf of modules along
restrictions of scalars agree on local sections. -/
lemma sectionsFunctor_map_comp_eqToHom_moduleSheaf_restrictScalars_symm_congr.{w₀, v₀, u₀}
    {C : Type u₀} [CategoryTheory.Category.{v₀} C] {J : CategoryTheory.GrothendieckTopology C}
    [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w₀})]
    {R R₁ R₂ : CategoryTheory.Sheaf J RingCat.{w₀}} (α₁ : R₁ ⟶ R) (α₂ : R₂ ⟶ R)
    (N : SheafOfModules.{w₀} R) {X : CategoryTheory.Sheaf J (Type w₀)}
    (g : X ⟶ CategoryTheory.Sheaf.moduleSheaf R N) (V : Cᵒᵖ)
    (x : (CategoryTheory.Sheaf.sectionsFunctor J V).obj X) :
    @Eq ↥(N.val.obj V)
      ((CategoryTheory.Sheaf.sectionsFunctor J V).map (g ≫ CategoryTheory.eqToHom
        (Stacks.Sheaves.RingedToposModules.moduleSheaf_restrictScalars α₁ N).symm) x)
      ((CategoryTheory.Sheaf.sectionsFunctor J V).map (g ≫ CategoryTheory.eqToHom
        (Stacks.Sheaves.RingedToposModules.moduleSheaf_restrictScalars α₂ N).symm) x) :=
  rfl

section FreeAlgebraDerivationExt

open CategoryTheory Stacks.Sites.FreeAlgebra

universe w₁ v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)

/-- **A derivation is determined by its values on the images of variables, along a locally
surjective map from a polynomial presheaf.** Let `α : A[E] ⟶ T` be a locally surjective
morphism of presheaves of commutative rings from the presheaf of polynomial rings in the
variables `E`, carrying the constants into the image of `r : R ⟶ T`. Two `R`-derivations of `T`
with values in a sheaf of modules which agree on the images of the variables are equal. -/
lemma derivation_ext_of_polynomial_variables (A : Sheaf J CommRingCat.{w₁})
    (E : Cᵒᵖ ⥤ Type w₁) {T R : Cᵒᵖ ⥤ CommRingCat.{w₁}} (α : polynomialPresheaf J A E ⟶ T)
    [Presheaf.IsLocallySurjective J α] (r : R ⟶ T) (c : A.obj ⟶ R)
    (hc : polynomialCoefficientMap J A E ≫ α = c ≫ r)
    {M : PresheafOfModules.{w₁} (T ⋙ forget₂ CommRingCat.{w₁} RingCat.{w₁})}
    (hM : Presheaf.IsSheaf J M.presheaf)
    (D₁ D₂ : PresheafOfModulesOfCommRing.Derivation' M r)
    (h : ∀ (X : Cᵒᵖ) (e : E.obj X),
      D₁.d (α.app X (MvPolynomial.X e)) = D₂.d (α.app X (MvPolynomial.X e))) : D₁ = D₂ := by
  refine AlgebraicGeometry.SheafOfModules.derivation_ext_of_isLocallySurjective J α hM D₁ D₂
    fun X p => ?_
  have hC : ∀ (D : PresheafOfModulesOfCommRing.Derivation' M r) (a : A.obj.obj X),
      D.d (α.app X (MvPolynomial.C a)) = 0 :=
    fun D a => by
      have e : α.app X (MvPolynomial.C a) = r.app X (c.app X a) :=
        congrArg (fun t : A.obj ⟶ T => t.app X a) hc
      rw [e]
      exact D.d_app _
  induction p using MvPolynomial.induction_on with
  | C a => exact (hC D₁ a).trans (hC D₂ a).symm
  | add p q hp hq =>
    refine Eq.trans (congrArg (fun t => D₁.d t) (map_add (ConcreteCategory.hom (α.app X)) p q)) ?_
    refine Eq.trans (map_add D₁.d _ _) ?_
    refine Eq.trans (congrArg₂ (· + ·) hp hq) ?_
    refine Eq.trans (map_add D₂.d _ _).symm ?_
    exact congrArg (fun t => D₂.d t) (map_add (ConcreteCategory.hom (α.app X)) p q).symm
  | mul_X p e hp =>
    refine Eq.trans (congrArg (fun t => D₁.d t)
      (map_mul (ConcreteCategory.hom (α.app X)) p (MvPolynomial.X e))) ?_
    refine Eq.trans (D₁.d_mul _ _) ?_
    refine Eq.trans (congrArg₂ (fun s t => _ • s + _ • t) (h X e) hp) ?_
    refine Eq.trans (D₂.d_mul _ _).symm ?_
    exact congrArg (fun t => D₂.d t)
      (map_mul (ConcreteCategory.hom (α.app X)) p (MvPolynomial.X e)).symm

variable [HasWeakSheafify J CommRingCat.{w₁}]

/-- A derivation of a free algebra sheaf `A[E]` over `A` is determined by its values on the
variables, when the sheafification of the presheaf of polynomial rings is locally surjective. -/
lemma freeAlgebraSheafDerivation_ext_of_variable
    (A : Sheaf J CommRingCat.{w₁}) (E : Cᵒᵖ ⥤ Type w₁)
    [Presheaf.IsLocallySurjective J
      ((toSheafification J CommRingCat.{w₁}).app (polynomialPresheaf J A E))]
    (M : _root_.SheafOfModules.{w₁}
      (Stacks.SheafOfModules.Tensor.ringSheaf (freeAlgebraSheaf J A E)))
    (D₁ D₂ : PresheafOfModulesOfCommRing.Derivation' M.val
      (freeAlgebraSheafCoefficientMap J A E).hom)
    (h : ∀ (X : Cᵒᵖ) (e : E.obj X),
      D₁.d ((freeAlgebraSheafVariable J A E).app X e) =
        D₂.d ((freeAlgebraSheafVariable J A E).app X e)) : D₁ = D₂ :=
  derivation_ext_of_polynomial_variables J A E
    ((toSheafification J CommRingCat.{w₁}).app (polynomialPresheaf J A E))
    (freeAlgebraSheafCoefficientMap J A E).hom (𝟙 _) rfl M.isSheaf D₁ D₂ h

end FreeAlgebraDerivationExt

section InverseImageBaseChange

universe u v w u' v' w'

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.SheafOfModules
open Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPullback
open Stacks.Sheaves.ToposPushforward
open CategoryTheory.Sheaf (inverseImageTargetModules)


variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasWeakSheafify J CommRingCat.{max u v w}] [HasWeakSheafify K CommRingCat.{max u' v' w'}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u' v' w'} RingCat.{max u' v' w'})]
  (f : MorphismOfTopoi (Sheaf J (Type (max u v w))) (Sheaf K (Type (max u' v' w'))))
  {A B : Sheaf K CommRingCat.{max u' v' w'}} (a : A ⟶ B)

/-- **The derivation attached to a morphism out of the inverse image of the degree-`0` term,
evaluated at a variable.** At the variable `[x]` of `(f⁻¹A)[f⁻¹B]` its value is the
transpose across `f⁻¹ ⊣ f_*` of the map `b ↦ D([b])` of sheaves of sets, `D` the
`A`-derivation of `A[B]` with values in the direct image attached to the morphism. -/
lemma inverseImageNaiveCotangentZeroDerivationEquiv_d_variable
    (M : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B)))
    (h : (inverseImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'} B)).obj
        (canonicalConormalSequence.{v', u', max u' v' w', max u' v' w'} K A B a).X₂ ⟶ M)
    (U : Cᵒᵖ) (x : (Sheaf.sectionsFunctor J U).obj
      (f.inverseImage.obj ((sheafCompose K (forget CommRingCat.{max u' v' w'})).obj B))) :
    (inverseImageNaiveCotangentZeroDerivationEquiv J K f a M h).d
        ((freeAlgebraSheafVariable J (f.inverseImageRing.obj A)
          (underlyingPresheaf J (f.inverseImageRing.obj B))).app U x) =
      (Sheaf.sectionsFunctor J U).map ((f.adj.homEquiv _ _).symm
        (variableSheaf K A B ≫ derivationSheafHom _ _
          ((pushforwardZeroDerivation J K f a M h).postcomp
            (directImageModulesRestrictScalarsIso f
              (presentationRingHom.{max u' v' w', v', u'} K (canonicalPresentation K A B a))
                M).hom.val))) x := by
  have hz : (freeAlgebraSheafVariable J (f.inverseImageRing.obj A)
        (underlyingPresheaf J (f.inverseImageRing.obj B))).app U x =
      (inverseImageFreeAlgebraIso f A B).hom.hom.app U
        ((Sheaf.sectionsFunctor J U).map (f.inverseImage.map (variableSheaf K A B)) x) :=
    (congrArg (fun m => (Sheaf.sectionsFunctor J U).map m x)
      (inverseImage_variableSheaf_comp_inverseImageFreeAlgebraHom f A B)).symm
  refine (congrArg (fun z => (inverseImageNaiveCotangentZeroDerivationEquiv J K f a M h).d z)
    hz).trans ?_
  refine (inverseImageNaiveCotangentZeroDerivationEquiv_d_freeAlgebraIso J K f a M h U _).trans ?_
  refine (inverseImageDerivationEquiv_symm_postcomp_d J K f a M
    (pushforwardZeroDerivation J K f a M h) _).symm.trans ?_
  have h1 := derivationSheafHom_inverseImageDerivationEquiv f
    (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B))
    ((_root_.SheafOfModules.restrictScalars
      (inverseImagePresentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f
        (canonicalPresentation K A B a))).obj M)
    ((inverseImageDerivationEquiv f
      (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B))
      ((_root_.SheafOfModules.restrictScalars
        (inverseImagePresentationRingHom.{max u v w, max u' v' w', v, u, v', u'} f
          (canonicalPresentation K A B a))).obj M)).symm
      ((pushforwardZeroDerivation J K f a M h).postcomp
        (directImageRestrictScalarsIso f (canonicalPresentation K A B a) M).hom.val))
  rw [Equiv.apply_symm_apply] at h1
  have h3 := (Equiv.eq_symm_apply _).2 h1.symm
  have h4 := congrArg (fun m => f.inverseImage.map (variableSheaf K A B) ≫ m) h3
  exact congrArg (fun m => (Sheaf.sectionsFunctor J U).map m x)
    (h4.trans (f.adj.homEquiv_naturality_left_symm _ _).symm)

variable {A' : Sheaf K CommRingCat.{max u' v' w'}} (a' : A' ⟶ B) (φ : A ⟶ A') (hf : a = φ ≫ a')

include hf in
/-- The change of base ring `B ⊗_{A[B]} Ω_{A[B]/A} ⟶ B ⊗_{A'[B]} Ω_{A'[B]/A'}` sends `1 ⊗ d[b]`
to `1 ⊗ d[b]`. -/
lemma naiveCotangentTensorMapOfBase_tensorDifferential_variable (V : Dᵒᵖ)
    (b : (underlyingPresheaf K B).obj V) :
    (naiveCotangentTensorMapOfBase.{v', u', max u' v' w', max u' v' w'}
        K A B a A' a' φ hf).val.app V
        (tensorDifferential.{v', u', max u' v' w', max u' v' w'} K A
          (freeAlgebraSheaf K A (underlyingPresheaf K B)) B
          (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B))
          (canonicalPresentation K A B a) V
          ((freeAlgebraSheafVariable K A (underlyingPresheaf K B)).app V b)) =
      tensorDifferential.{v', u', max u' v' w', max u' v' w'} K A'
          (freeAlgebraSheaf K A' (underlyingPresheaf K B)) B
          (freeAlgebraSheafCoefficientMap K A' (underlyingPresheaf K B))
          (canonicalPresentation K A' B a') V
          ((freeAlgebraSheafVariable K A' (underlyingPresheaf K B)).app V b) := by
  refine (tensorSheafMapOfSquare_tensorDifferential.{v', u', max u' v' w', max u' v' w'} K A A'
    (freeAlgebraSheaf K A (underlyingPresheaf K B)) (freeAlgebraSheaf K A' (underlyingPresheaf K B))
    B B (freeAlgebraSheafCoefficientMap K A _) (freeAlgebraSheafCoefficientMap K A' _)
    (canonicalPresentation K A B a) (canonicalPresentation K A' B a')
    (canonicalFreeAlgebraMapOfSquare K A A' B B φ (𝟙 B)) (𝟙 B) φ
    (freeAlgebraMapOfSquare_comp_canonicalPresentation K A A' B B a a' φ (𝟙 B)
      (comp_id_eq_comp_of_fac K A B a A' a' φ hf))
    (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMapOfSquare K A A' _ _ φ
      (underlyingPresheafMap K B B (𝟙 B))).symm V _).trans ?_
  exact congrArg _ (congrArg (fun t => t.app V b)
    (freeAlgebraSheafVariable_comp_freeAlgebraMapOfSquare K A A' _ _ φ
      (underlyingPresheafMap K B B (𝟙 B))))

omit [HasWeakSheafify J CommRingCat] [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
include hf in
/-- **The derivation attached to a morphism out of the inverse image of the degree-`0` term is
natural in the base ring, on variables.** Precomposing with the inverse image of the change of
base ring `B ⊗_{A[B]} Ω_{A[B]/A} ⟶ B ⊗_{A'[B]} Ω_{A'[B]/A'}` does not change its value at the
variable `[b]`. -/
lemma pushforwardZeroDerivation_d_variable_naturality
    (M : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B)))
    (h : (inverseImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'} B)).obj
        (canonicalConormalSequence.{v', u', max u' v' w', max u' v' w'} K A' B a').X₂ ⟶ M)
    (V : Dᵒᵖ) (b : (underlyingPresheaf K B).obj V) :
    (pushforwardZeroDerivation J K f a M
        ((inverseImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'} B)).map
          (naiveCotangentTensorMapOfBase.{v', u', max u' v' w', max u' v' w'} K A B a A' a' φ hf)
          ≫ h)).d ((freeAlgebraSheafVariable K A (underlyingPresheaf K B)).app V b) =
      (pushforwardZeroDerivation J K f a' M h).d
        ((freeAlgebraSheafVariable K A' (underlyingPresheaf K B)).app V b) := by
  unfold pushforwardZeroDerivation inverseImageZeroStep₂
  rw [naiveCotangentZeroDerivationEquiv_d, naiveCotangentZeroDerivationEquiv_d]
  have hn := toposModulesHomEquiv_naturality_left f (Tensor.ringSheaf.{u', v', max u' v' w'} B)
    (naiveCotangentTensorMapOfBase.{v', u', max u' v' w', max u' v' w'} K A B a A' a' φ hf) h
  unfold inverseImageZeroStep₁
  rw [hn]
  have hT := naiveCotangentTensorMapOfBase_tensorDifferential_variable K a a' φ hf V b
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.hom_comp,
    LinearMap.comp_apply]
  rw [hT]

/-- **The derivation attached to a morphism out of the inverse image of the degree-`0` term,
evaluated at a variable**, with the comparison of the direct image with restriction of scalars
removed: the value is the transpose of `b ↦ D([b])`, read through identities of underlying
sheaves of sets. -/
lemma inverseImageNaiveCotangentZeroDerivationEquiv_d_variable'
    (M : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B)))
    (h : (inverseImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'} B)).obj
        (canonicalConormalSequence.{v', u', max u' v' w', max u' v' w'} K A B a).X₂ ⟶ M)
    (U : Cᵒᵖ) (x : (Sheaf.sectionsFunctor J U).obj
      (f.inverseImage.obj ((sheafCompose K (forget CommRingCat.{max u' v' w'})).obj B))) :
    (inverseImageNaiveCotangentZeroDerivationEquiv J K f a M h).d
        ((freeAlgebraSheafVariable J (f.inverseImageRing.obj A)
          (underlyingPresheaf J (f.inverseImageRing.obj B))).app U x) =
      (Sheaf.sectionsFunctor J U).map ((f.adj.homEquiv _ _).symm
        ((variableSheaf K A B ≫ derivationSheafHom _ _ (pushforwardZeroDerivation J K f a M h)) ≫
          eqToHom (moduleSheaf_restrictScalars_directImageModules f
            (presentationRingHom.{max u' v' w', v', u'} K (canonicalPresentation K A B a)) M)) ≫
        eqToHom (Stacks.Sheaves.RingedToposModules.moduleSheaf_restrictScalars
          (inverseImageRingMap f
            (presentationRingHom.{max u' v' w', v', u'} K (canonicalPresentation K A B a))) M).symm)
        x := by
  refine (inverseImageNaiveCotangentZeroDerivationEquiv_d_variable J K f a M h U x).trans ?_
  have e1 := derivationSheafHom_postcomp.{max u' v' w', v', u'}
      (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B))
      (directImageModulesRestrictScalarsIso f
        (presentationRingHom.{max u' v' w', v', u'} K (canonicalPresentation K A B a)) M).hom
      (pushforwardZeroDerivation J K f a M h)
  have e3 := homEquiv_symm_comp_moduleSheafFunctor_map_directImageModulesRestrictScalarsIso f
    (presentationRingHom.{max u' v' w', v', u'} K (canonicalPresentation K A B a)) M
    (variableSheaf K A B ≫ derivationSheafHom _ _ (pushforwardZeroDerivation J K f a M h))
  have e2 : variableSheaf K A B ≫ derivationSheafHom _ _
      ((pushforwardZeroDerivation J K f a M h).postcomp
        (directImageModulesRestrictScalarsIso f
          (presentationRingHom.{max u' v' w', v', u'} K (canonicalPresentation K A B a))
            M).hom.val) =
      (variableSheaf K A B ≫ derivationSheafHom _ _ (pushforwardZeroDerivation J K f a M h)) ≫
        (Sheaf.moduleSheafFunctor _).map (directImageModulesRestrictScalarsIso f
          (presentationRingHom.{max u' v' w', v', u'} K (canonicalPresentation K A B a)) M).hom :=
    (congrArg (variableSheaf K A B ≫ ·) e1).trans (Category.assoc _ _ _).symm
  exact congrArg (fun m => (Sheaf.sectionsFunctor J U).map m x)
    ((congrArg (f.adj.homEquiv _ _).symm e2).trans e3)

/-- **The values at the variables of the derivation attached to a morphism out of the inverse
image of the degree-`0` term**, as a morphism of sheaves of sets into the direct image of the
underlying sheaf of sets of the target: `b ↦ D([b])`. -/
noncomputable def pushforwardZeroVariableHom
    (M : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B)))
    (h : (inverseImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'} B)).obj
        (canonicalConormalSequence.{v', u', max u' v' w', max u' v' w'} K A B a).X₂ ⟶ M) :
    (sheafCompose K (forget CommRingCat.{max u' v' w'})).obj B ⟶
      f.pushforward.obj (Sheaf.moduleSheaf
        (inverseImageRingSheaf f (Tensor.ringSheaf.{u', v', max u' v' w'} B)) M) :=
  (variableSheaf K A B ≫ derivationSheafHom _ _ (pushforwardZeroDerivation J K f a M h)) ≫
    eqToHom (moduleSheaf_restrictScalars_directImageModules f
      (O' := Tensor.ringSheaf.{u', v', max u' v' w'}
        (freeAlgebraSheaf K A (underlyingPresheaf K B)))
      ((Stacks.forgetCommRingSheaf.{v', u', max u' v' w'} K).map (canonicalPresentation K A B a)) M)

omit [HasWeakSheafify J CommRingCat] [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
include hf in
/-- **The values at the variables are natural in the base ring.** -/
lemma pushforwardZeroVariableHom_naturality
    (M : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B)))
    (k : (inverseImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'} B)).obj
        (canonicalConormalSequence.{v', u', max u' v' w', max u' v' w'} K A' B a').X₂ ⟶ M) :
    pushforwardZeroVariableHom J K f a M
        ((inverseImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'} B)).map
          (naiveCotangentTensorMapOfBase.{v', u', max u' v' w', max u' v' w'} K A B a A' a' φ hf)
          ≫ k) =
      pushforwardZeroVariableHom J K f a' M k := by
  refine Sheaf.hom_ext_sections fun V b => ?_
  unfold pushforwardZeroVariableHom
  rw [(Sheaf.sectionsFunctor K V).map_comp_apply, (Sheaf.sectionsFunctor K V).map_comp_apply]
  refine sectionsFunctor_map_eqToHom_moduleSheaf_restrictScalars_directImageModules_congr f
    (M := M) _ _ V _ _ ?_
  have h1 := sectionsFunctor_map_variableSheaf_comp_derivationSheafHom K A B _
    (pushforwardZeroDerivation J K f a M
        ((inverseImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'} B)).map
          (naiveCotangentTensorMapOfBase.{v', u', max u' v' w', max u' v' w'} K A B a A' a' φ hf)
          ≫ k)) V b
  have h2 := sectionsFunctor_map_variableSheaf_comp_derivationSheafHom K A' B _
    (pushforwardZeroDerivation J K f a' M k) V b
  have h3 := pushforwardZeroDerivation_d_variable_naturality J K f a a' φ hf M k V b
  exact h1.trans (h3.trans h2.symm)

/-- **The derivation attached to a morphism out of the inverse image of the degree-`0` term,
at a variable**, through `pushforwardZeroVariableHom`. -/
lemma inverseImageNaiveCotangentZeroDerivationEquiv_d_variable''
    (M : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B)))
    (h : (inverseImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'} B)).obj
        (canonicalConormalSequence.{v', u', max u' v' w', max u' v' w'} K A B a).X₂ ⟶ M)
    (U : Cᵒᵖ) (x : (Sheaf.sectionsFunctor J U).obj
      (f.inverseImage.obj ((sheafCompose K (forget CommRingCat.{max u' v' w'})).obj B))) :
    (inverseImageNaiveCotangentZeroDerivationEquiv J K f a M h).d
        ((freeAlgebraSheafVariable J (f.inverseImageRing.obj A)
          (underlyingPresheaf J (f.inverseImageRing.obj B))).app U x) =
      (Sheaf.sectionsFunctor J U).map ((f.adj.homEquiv _ _).symm
        (pushforwardZeroVariableHom J K f a M h) ≫
        eqToHom (Stacks.Sheaves.RingedToposModules.moduleSheaf_restrictScalars
          (inverseImageRingMap f
            (presentationRingHom.{max u' v' w', v', u'} K (canonicalPresentation K A B a))) M).symm)
        x :=
  inverseImageNaiveCotangentZeroDerivationEquiv_d_variable' J K f a M h U x

include hf in
/-- **The derivation attached to a morphism out of the inverse image of the degree-`0` term is
natural in the base ring**: precomposing with the inverse image of the change of base ring does
not change its value at a variable. -/
lemma inverseImageNaiveCotangentZeroDerivationEquiv_d_variable_naturality
    (M : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B)))
    (k : (inverseImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'} B)).obj
        (canonicalConormalSequence.{v', u', max u' v' w', max u' v' w'} K A' B a').X₂ ⟶ M)
    (U : Cᵒᵖ) (x : (Sheaf.sectionsFunctor J U).obj
      (f.inverseImage.obj ((sheafCompose K (forget CommRingCat.{max u' v' w'})).obj B))) :
    (inverseImageNaiveCotangentZeroDerivationEquiv J K f a M
        ((inverseImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'} B)).map
          (naiveCotangentTensorMapOfBase.{v', u', max u' v' w', max u' v' w'} K A B a A' a' φ hf)
          ≫ k)).d
        ((freeAlgebraSheafVariable J (f.inverseImageRing.obj A)
          (underlyingPresheaf J (f.inverseImageRing.obj B))).app U x) =
      (inverseImageNaiveCotangentZeroDerivationEquiv J K f a' M k).d
        ((freeAlgebraSheafVariable J (f.inverseImageRing.obj A')
          (underlyingPresheaf J (f.inverseImageRing.obj B))).app U x) := by
  have h1 := inverseImageNaiveCotangentZeroDerivationEquiv_d_variable'' J K f a M
    ((inverseImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'} B)).map
      (naiveCotangentTensorMapOfBase.{v', u', max u' v' w', max u' v' w'} K A B a A' a' φ hf)
      ≫ k) U x
  have h2 := inverseImageNaiveCotangentZeroDerivationEquiv_d_variable'' J K f a' M k U x
  rw [pushforwardZeroVariableHom_naturality J K f a a' φ hf M k] at h1
  have h3 := sectionsFunctor_map_comp_eqToHom_moduleSheaf_restrictScalars_symm_congr
    (inverseImageRingMap f
      (presentationRingHom.{max u' v' w', v', u'} K (canonicalPresentation K A B a)))
    (inverseImageRingMap f
      (presentationRingHom.{max u' v' w', v', u'} K (canonicalPresentation K A' B a'))) M
    ((f.adj.homEquiv _ _).symm (pushforwardZeroVariableHom J K f a' M k)) U x
  exact h1.trans (h3.trans h2.symm)

omit [HasWeakSheafify J CommRingCat] [HasWeakSheafify K CommRingCat]
  [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [K.HasSheafCompose (forget₂ CommRingCat RingCat)] in
include hf in
/-- The inverse image of a factorisation `a = φ ≫ a'` is a factorisation. -/
lemma inverseImageRing_map_fac :
    f.inverseImageRing.map a = f.inverseImageRing.map φ ≫ f.inverseImageRing.map a' := by
  rw [hf, Functor.map_comp]

include hf in
/-- **Stacks 08TZ is natural in the base ring, in degree `0`.** For a factorisation
`a = φ ≫ a'` of `a : A ⟶ B` through `a' : A' ⟶ B`, the inverse image of the change of base ring
`B ⊗_{A[B]} Ω_{A[B]/A} ⟶ B ⊗_{A'[B]} Ω_{A'[B]/A'}`, read through the two degree `0`
comparisons, is the change of base ring for `f⁻¹a = f⁻¹φ ≫ f⁻¹a'`. -/
theorem inverseImageNaiveCotangentZeroTargetIso_naturality
    [J.WEqualsLocallyBijective CommRingCat.{max u v w}] :
    (inverseImageTargetModules.{u, v, w, u', v', w'} J K f (B := B)).map
        (naiveCotangentTensorMapOfBase.{v', u', max u' v' w', max u' v' w'} K A B a A' a' φ hf) ≫
      (inverseImageNaiveCotangentZeroTargetIso J K f a').hom =
    (inverseImageNaiveCotangentZeroTargetIso J K f a).hom ≫
      naiveCotangentTensorMapOfBase.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A)
        (f.inverseImageRing.obj B) (f.inverseImageRing.map a) (f.inverseImageRing.obj A')
        (f.inverseImageRing.map a') (f.inverseImageRing.map φ)
        (inverseImageRing_map_fac J K f a a' φ hf) := by
  apply (inverseImageNaiveCotangentZeroDerivationEquiv J K f a _).injective
  have hpoly : Presheaf.IsLocallySurjective J
      ((toSheafification J CommRingCat.{max u v w}).app (polynomialPresheaf J
        (f.inverseImageRing.obj A) (underlyingPresheaf J (f.inverseImageRing.obj B)))) :=
    (J.W_toSheafify _).isLocallySurjective
  refine freeAlgebraSheafDerivation_ext_of_variable J _ _ _ _ _ fun U x => ?_
  have hL := inverseImageNaiveCotangentZeroDerivationEquiv_d_variable_naturality J K f a a' φ hf _
    (inverseImageNaiveCotangentZeroTargetIso J K f a').hom U x
  refine hL.trans ?_
  have key₁ := fun (A₀ : Sheaf K CommRingCat.{max u' v' w'}) (a₀ : A₀ ⟶ B)
      (p : (freeAlgebraSheaf J (f.inverseImageRing.obj A₀)
        (underlyingPresheaf J (f.inverseImageRing.obj B))).obj.obj U) =>
    congrArg (fun D => D.d p) (inverseImageNaiveCotangentZeroTargetIso_derivation J K f a₀)
  have key₂ := fun (A₀ : Sheaf K CommRingCat.{max u' v' w'}) (a₀ : A₀ ⟶ B)
      (p : (freeAlgebraSheaf J (f.inverseImageRing.obj A₀)
        (underlyingPresheaf J (f.inverseImageRing.obj B))).obj.obj U) =>
    naiveCotangentZeroDerivationEquiv_d J (f.inverseImageRing.obj A₀)
      (f.inverseImageRing.obj B) (f.inverseImageRing.map a₀)
      (canonicalConormalSequence.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A₀)
        (f.inverseImageRing.obj B) (f.inverseImageRing.map a₀)).X₂ (𝟙 _) U p
  have hN := congrArg (fun D => D.d ((freeAlgebraSheafVariable J (f.inverseImageRing.obj A)
      (underlyingPresheaf J (f.inverseImageRing.obj B))).app U x))
    (inverseImageNaiveCotangentZeroDerivationEquiv_naturality J K f a
      (inverseImageNaiveCotangentZeroTargetIso J K f a).hom
      (naiveCotangentTensorMapOfBase.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A)
        (f.inverseImageRing.obj B) (f.inverseImageRing.map a) (f.inverseImageRing.obj A')
        (f.inverseImageRing.map a') (f.inverseImageRing.map φ)
        (inverseImageRing_map_fac J K f a a' φ hf)))
  have hT := naiveCotangentTensorMapOfBase_tensorDifferential_variable.{u, v, w}
    J (f.inverseImageRing.map a) (f.inverseImageRing.map a')
    (f.inverseImageRing.map φ) (inverseImageRing_map_fac J K f a a' φ hf) U x
  exact ((key₁ A' a' _).trans (key₂ A' a' _)).trans
    (hT.symm.trans ((congrArg
    ((naiveCotangentTensorMapOfBase.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A)
        (f.inverseImageRing.obj B) (f.inverseImageRing.map a) (f.inverseImageRing.obj A')
        (f.inverseImageRing.map a') (f.inverseImageRing.map φ)
        (inverseImageRing_map_fac J K f a a' φ hf)).val.app U)
      ((key₁ A a _).trans (key₂ A a _)).symm).trans hN.symm))

end InverseImageBaseChange

end Stacks.SheafOfModules

end
