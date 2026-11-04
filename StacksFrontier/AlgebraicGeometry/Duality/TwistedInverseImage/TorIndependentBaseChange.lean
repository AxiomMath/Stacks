module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BaseChange
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.Composition
public import StacksFrontier.CategoryTheory.Adjunction.PushedForwardTwistedBaseChange
public import StacksFrontier.CategoryTheory.Adjunction.LiftedConjugate
public import StacksFrontier.CategoryTheory.Adjunction.RestrictMates

/-!
# The twisted inverse image and base change of derived direct image

For a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

the transformation `ξ : Rg'_* ∘ a' ⟶ a ∘ Rg_*` of [Stacks, Tag 0A9K] is, up to the identification
of iterated mates with conjugates, the base change map `Lg^* ∘ Rf_* ⟶ Rf'_* ∘ L(g')^*` of derived
direct image on `D_QCoh`. Hence `ξ` is invertible as soon as that base change map is.

## Main definitions

* `Stacks.Duality.quasiCoherentDerivedBaseChange` — the base change map
  `Rf_* ⋙ Lg^* ⟶ L(g')^* ⋙ Rf'_*` on the quasi-coherent derived categories, the mate of the
  comparison of derived direct images around the square.

## Main results

* `Stacks.Duality.isIso_twistedInverseImagePushforwardBaseChange_of_isIso` — `ξ` is invertible
  when the base change map is.
* `Stacks.Duality.quasiCoherentDerivedPushforwardSquareIso_hom_eq` — the same on `D_QCoh`, for the
  restricted adjunctions.
* `Stacks.Duality.derivedPushforwardSquareIso_hom_eq` — the comparison of derived direct images
  around a commutative square is the conjugate of the comparison of the derived pullbacks.
* `Stacks.Duality.quasiCoherentDerivedAdjunction_unit_app_hom`,
  `Stacks.Duality.quasiCoherentDerivedAdjunction_counit_app_hom` — the unit and counit of the
  restricted adjunction are the ambient ones.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

variable {X' X Y' Y : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
  (hpushg' : ∀ (K : quasiCoherentDerivedCategory X') (i : ℤ),
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((derivedPushforward g').obj K.obj)).IsQuasicoherent)
  (hpushf : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
  (hpushf' : ∀ (K : quasiCoherentDerivedCategory X') (i : ℤ),
    ((DerivedCategory.homologyFunctor Y'.Modules i).obj
      ((derivedPushforward f').obj K.obj)).IsQuasicoherent)
  (hpushg : ∀ (K : quasiCoherentDerivedCategory Y') (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward g).obj K.obj)).IsQuasicoherent)
  (hpullg : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y'.Modules i).obj
      ((derivedPullback g).obj K.obj)).IsQuasicoherent)
  (hpullg' : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor X'.Modules i).obj
      ((derivedPullback g').obj K.obj)).IsQuasicoherent)

/-- The counit of the restricted adjunction `Lf^* ⊣ Rf_*` on `D_QCoh` is the ambient counit. -/
theorem quasiCoherentDerivedAdjunction_counit_app_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hpull : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
      ((DerivedCategory.homologyFunctor X.Modules i).obj
        ((derivedPullback f).obj K.obj)).IsQuasicoherent)
    (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
    (K : quasiCoherentDerivedCategory X) :
    ((quasiCoherentDerivedAdjunction f hpull hpush).counit.app K).hom =
      (derivedAdjunction f).counit.app K.obj := by
  have h := Adjunction.map_restrictFullyFaithful_counit_app (derivedAdjunction f)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (quasiCoherentDerivedPullbackCompιIso f hpull).symm
    (DerivedPushforward.quasiCoherentDerivedPushforwardCompιIso f hpush).symm K
  simp only [Iso.symm_hom, Iso.symm_inv] at h
  refine h.trans ?_
  show 𝟙 _ ≫ (derivedPullback f).map (𝟙 _) ≫ _ = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
  rfl

/-- The unit of the restricted adjunction `Lf^* ⊣ Rf_*` on `D_QCoh` is the ambient unit. -/
theorem quasiCoherentDerivedAdjunction_unit_app_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hpull : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
      ((DerivedCategory.homologyFunctor X.Modules i).obj
        ((derivedPullback f).obj K.obj)).IsQuasicoherent)
    (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
    (K : quasiCoherentDerivedCategory Y) :
    ((quasiCoherentDerivedAdjunction f hpull hpush).unit.app K).hom =
      (derivedAdjunction f).unit.app K.obj := by
  have h := Adjunction.map_restrictFullyFaithful_unit_app (derivedAdjunction f)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (quasiCoherentDerivedPullbackCompιIso f hpull).symm
    (DerivedPushforward.quasiCoherentDerivedPushforwardCompιIso f hpush).symm K
  simp only [Iso.symm_hom, Iso.symm_inv] at h
  refine h.trans ?_
  show _ ≫ (derivedPushforward f).map (𝟙 _) ≫ 𝟙 _ = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rfl

/-- **The composition isomorphism of derived direct image is the conjugate of that of derived
pullback.** -/
theorem derivedPushforwardCompIso_hom_eq {X Y Z : Scheme.{u}} (f₁ : X ⟶ Y) (f₂ : Y ⟶ Z) :
    (derivedPushforwardCompIso f₁ f₂).hom =
      conjugateEquiv ((derivedAdjunction f₂).comp (derivedAdjunction f₁))
        (derivedAdjunction (f₁ ≫ f₂)) (derivedPullbackCompIso f₁ f₂).inv :=
  Stacks.CategoryTheory.rightAdjointUniq_ofNatIsoLeft_left_hom _ _ _

/-- The inverse of the composition isomorphism of derived direct image is the conjugate of the
composition isomorphism of derived pullback. -/
theorem derivedPushforwardCompIso_inv_eq {X Y Z : Scheme.{u}} (f₁ : X ⟶ Y) (f₂ : Y ⟶ Z) :
    (derivedPushforwardCompIso f₁ f₂).inv =
      conjugateEquiv (derivedAdjunction (f₁ ≫ f₂))
        ((derivedAdjunction f₂).comp (derivedAdjunction f₁))
        (derivedPullbackCompIso f₁ f₂).hom := by
  rw [← cancel_epi (derivedPushforwardCompIso f₁ f₂).hom, Iso.hom_inv_id,
    derivedPushforwardCompIso_hom_eq, conjugateEquiv_comp, Iso.hom_inv_id, conjugateEquiv_id]

/-- **Transport of derived direct image along an equality of morphisms is the conjugate of
transport of derived pullback.** -/
theorem eqToHom_derivedPushforward_eq {X Y : Scheme.{u}} {h₁ h₂ : X ⟶ Y} (e : h₁ = h₂) :
    eqToHom (congrArg (fun h : X ⟶ Y => derivedPushforward h) e) =
      conjugateEquiv (derivedAdjunction h₁) (derivedAdjunction h₂)
        (eqToHom (congrArg (fun h : X ⟶ Y => derivedPullback h) e.symm)) := by
  subst e
  simp only [eqToHom_refl, conjugateEquiv_id]

/-- **The comparison of derived direct images around a commutative square is the conjugate of
the comparison of the derived pullbacks.** -/
theorem derivedPushforwardSquareIso_hom_eq (w : g' ≫ f = f' ≫ g) :
    (derivedPushforwardSquareIso g' f' f g w).hom =
      conjugateEquiv ((derivedAdjunction f).comp (derivedAdjunction g'))
        ((derivedAdjunction g).comp (derivedAdjunction f'))
        ((derivedPullbackCompIso f' g).hom ≫
          eqToHom (congrArg (fun h : X' ⟶ Y => derivedPullback h) w.symm) ≫
            (derivedPullbackCompIso g' f).inv) := by
  rw [derivedPushforwardSquareIso, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, eqToIso.hom,
    derivedPushforwardCompIso_hom_eq, eqToHom_derivedPushforward_eq,
    derivedPushforwardCompIso_inv_eq,
    conjugateEquiv_comp, conjugateEquiv_comp, Category.assoc]
  exact w

/-- The underlying morphism of the image of `φ` under the restricted derived pullback
`quasiCoherentDerivedPullback h hpull` is its image under `derivedPullback h`. -/
theorem quasiCoherentDerivedPullback_map_hom {X Y : Scheme.{u}} (h : X ⟶ Y)
    (hpull : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
      ((DerivedCategory.homologyFunctor X.Modules i).obj
        ((derivedPullback h).obj K.obj)).IsQuasicoherent)
    {K L : quasiCoherentDerivedCategory Y} (φ : K ⟶ L) :
    ((quasiCoherentDerivedPullback h hpull).map φ).hom = (derivedPullback h).map φ.hom :=
  rfl

/-- The component at `d` of the comparison `quasiCoherentDerivedPushforwardSquareIso` has as
underlying morphism the component of `derivedPushforwardSquareIso` at `d.obj`. -/
theorem quasiCoherentDerivedPushforwardSquareIso_hom_app_hom (w : g' ≫ f = f' ≫ g)
    (d : quasiCoherentDerivedCategory X') :
    ((quasiCoherentDerivedPushforwardSquareIso g' f' f g hpushg' hpushf hpushf' hpushg w).hom.app
      d).hom = (derivedPushforwardSquareIso g' f' f g w).hom.app d.obj :=
  rfl

/-- The component at `K` of `(quasiCoherentDerivedPullbackCompIso f₁ f₂).hom` has as underlying
morphism the component of `(derivedPullbackCompIso f₁ f₂).hom` at `K.obj`. -/
theorem quasiCoherentDerivedPullbackCompIso_hom_app_hom {X Y Z : Scheme.{u}} (f₁ : X ⟶ Y)
    (f₂ : Y ⟶ Z) (K : quasiCoherentDerivedCategory Z) :
    ((quasiCoherentDerivedPullbackCompIso f₁ f₂).hom.app K).hom =
      (derivedPullbackCompIso f₁ f₂).hom.app K.obj :=
  rfl

/-- The component at `K` of `(quasiCoherentDerivedPullbackCompIso f₁ f₂).inv` has as underlying
morphism the component of `(derivedPullbackCompIso f₁ f₂).inv` at `K.obj`. -/
theorem quasiCoherentDerivedPullbackCompIso_inv_app_hom {X Y Z : Scheme.{u}} (f₁ : X ⟶ Y)
    (f₂ : Y ⟶ Z) (K : quasiCoherentDerivedCategory Z) :
    ((quasiCoherentDerivedPullbackCompIso f₁ f₂).inv.app K).hom =
      (derivedPullbackCompIso f₁ f₂).inv.app K.obj :=
  rfl

/-- The component at `K` of `(quasiCoherentDerivedPullbackCongr e).inv` has as underlying
morphism the transport along `e.symm` of `(derivedPullback h).obj K.obj`. -/
theorem quasiCoherentDerivedPullbackCongr_inv_app_hom {X Y : Scheme.{u}} {h₁ h₂ : X ⟶ Y}
    (e : h₁ = h₂) (K : quasiCoherentDerivedCategory Y) :
    ((quasiCoherentDerivedPullbackCongr e).inv.app K).hom =
      eqToHom (congrArg (fun h : X ⟶ Y => (derivedPullback h).obj K.obj) e.symm) :=
  rfl

/-- The restricted adjunction `Lf^* ⊣ Rf_*` on `D_QCoh` corresponds on counits to the ambient
one, through the identity commutation isomorphisms of the restrictions. -/
theorem counit_comm_quasiCoherentDerivedAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hpull : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
      ((DerivedCategory.homologyFunctor X.Modules i).obj
        ((derivedPullback f).obj K.obj)).IsQuasicoherent)
    (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
    (K : quasiCoherentDerivedCategory X) :
    (quasiCoherentDerivedPullbackCompιIso f hpull).symm.hom.app
        ((quasiCoherentDerivedPushforward f hpush).obj K) ≫
      (ObjectProperty.ι _).map ((quasiCoherentDerivedAdjunction f hpull hpush).counit.app K) =
      (derivedPullback f).map
          ((DerivedPushforward.quasiCoherentDerivedPushforwardCompιIso f hpush).symm.inv.app K) ≫
        (derivedAdjunction f).counit.app ((ObjectProperty.ι _).obj K) :=
  CategoryTheory.counit_comm_restrictFullyFaithful (derivedAdjunction f) _ _ _ _ K

/-- The square of composite derived pullbacks on `D_QCoh` has the ambient components. -/
theorem squareCompositeIso_quasiCoherentDerivedPullbackCompIso_hom_app_hom (w : g' ≫ f = f' ≫ g)
    (K : quasiCoherentDerivedCategory Y) :
    ((Stacks.AffineProjectionFormula.squareCompositeIso (quasiCoherentDerivedPullbackCompIso f' g)
      (quasiCoherentDerivedPullbackCompIso g' f ≪≫ quasiCoherentDerivedPullbackCongr w)).hom.app
        K).hom =
      ((derivedPullbackCompIso f' g).hom ≫
        eqToHom (congrArg (fun h : X' ⟶ Y => derivedPullback h) w.symm) ≫
          (derivedPullbackCompIso g' f).inv).app K.obj := by
  have e : ((derivedPullbackCompIso f' g).hom ≫
      eqToHom (congrArg (fun h : X' ⟶ Y => derivedPullback h) w.symm) ≫
        (derivedPullbackCompIso g' f).inv).app K.obj =
      (derivedPullbackCompIso f' g).hom.app K.obj ≫
        eqToHom (congrArg (fun h : X' ⟶ Y => (derivedPullback h).obj K.obj) w.symm) ≫
          (derivedPullbackCompIso g' f).inv.app K.obj := by
    rw [NatTrans.comp_app, NatTrans.comp_app, eqToHom_app]
  rw [e]
  rfl

/-- **The comparison of derived direct images around a commutative square on `D_QCoh` is the
conjugate of the comparison of the composite derived pullbacks**, in the shape of
`Stacks.CategoryTheory.BaseChange.composedPushforwardSquare`. -/
theorem quasiCoherentDerivedPushforwardSquareIso_hom_eq (w : g' ≫ f = f' ≫ g) :
    (quasiCoherentDerivedPushforwardSquareIso g' f' f g hpushg' hpushf hpushf' hpushg w).hom =
      (Stacks.CategoryTheory.BaseChange.composedPushforwardSquare
        (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f) hpushf)
        (quasiCoherentDerivedAdjunction f' (isQuasicoherent_homology_derivedPullback' f') hpushf')
        (quasiCoherentDerivedAdjunction g (isQuasicoherent_homology_derivedPullback' g) hpushg)
        (quasiCoherentDerivedAdjunction g' (isQuasicoherent_homology_derivedPullback' g') hpushg')
        (quasiCoherentDerivedPullbackCompIso f' g)
        (quasiCoherentDerivedPullbackCompIso g' f ≪≫
          quasiCoherentDerivedPullbackCongr w)).natTrans :=
  ObjectProperty.eq_conjugateEquiv_restrict_comp (derivedAdjunction f) (derivedAdjunction f')
    (derivedAdjunction g) (derivedAdjunction g') _ hpushf _ hpushf' _ hpushg _ hpushg' _ _
    (squareCompositeIso_quasiCoherentDerivedPullbackCompIso_hom_app_hom g' f' f g w) _
    (fun d => (quasiCoherentDerivedPushforwardSquareIso_hom_app_hom g' f' f g hpushg' hpushf
      hpushf' hpushg w d).trans (by rw [derivedPushforwardSquareIso_hom_eq]))

/-- **The base change map of derived direct image on `D_QCoh`**, `Rf_* ⋙ Lg^* ⟶ L(g')^* ⋙ Rf'_*`
for a commutative square: the mate, under `Lg^* ⊣ Rg_*` and `L(g')^* ⊣ Rg'_*`, of the comparison
`Rg'_* ⋙ Rf_* ≅ Rf'_* ⋙ Rg_*` of derived direct images around the square. -/
def quasiCoherentDerivedBaseChange (w : g' ≫ f = f' ≫ g) :
    TwoSquare (quasiCoherentDerivedPushforward f hpushf) (quasiCoherentDerivedPullback g' hpullg')
      (quasiCoherentDerivedPullback g hpullg) (quasiCoherentDerivedPushforward f' hpushf') :=
  (mateEquiv (quasiCoherentDerivedAdjunction g' hpullg' hpushg')
    (quasiCoherentDerivedAdjunction g hpullg hpushg)).symm
      (quasiCoherentDerivedPushforwardSquareIso g' f' f g hpushg' hpushf hpushf' hpushg w).hom

/-- **The base change map of derived direct image on `D_QCoh` is the horizontal mate of the
comparison of the composite derived pullbacks**, `Stacks.CategoryTheory.BaseChange.twoSquare`. -/
theorem quasiCoherentDerivedBaseChange_eq_twoSquare (w : g' ≫ f = f' ≫ g) :
    quasiCoherentDerivedBaseChange g' f' f g hpushg' hpushf hpushf' hpushg
      (isQuasicoherent_homology_derivedPullback' g) (isQuasicoherent_homology_derivedPullback' g')
      w =
      Stacks.CategoryTheory.BaseChange.twoSquare
        (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f) hpushf)
        (quasiCoherentDerivedAdjunction f' (isQuasicoherent_homology_derivedPullback' f') hpushf')
        (quasiCoherentDerivedPullbackCompIso f' g)
        (quasiCoherentDerivedPullbackCompIso g' f ≪≫ quasiCoherentDerivedPullbackCongr w) := by
  apply (mateEquiv (quasiCoherentDerivedAdjunction g' (isQuasicoherent_homology_derivedPullback' g')
    hpushg') (quasiCoherentDerivedAdjunction g (isQuasicoherent_homology_derivedPullback' g)
      hpushg)).injective
  refine (Equiv.apply_symm_apply _ _).trans ?_
  rw [← Stacks.CategoryTheory.BaseChange.composedPushforwardSquare_eq_mateEquiv]
  exact quasiCoherentDerivedPushforwardSquareIso_hom_eq g' f' f g hpushg' hpushf hpushf' hpushg w

variable [(quasiCoherentDerivedPushforward f hpushf).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward f' hpushf').IsLeftAdjoint]

/-- **`ξ` is the conjugate of the base change map**: under the composite adjunctions
`L(g')^* ⋙ Rf'_* ⊣ a' ⋙ Rg'_*` and `Rf_* ⋙ Lg^* ⊣ Rg_* ⋙ a`, the transformation
`ξ : Rg'_* ∘ a' ⟶ a ∘ Rg_*` corresponds to `Rf_* ⋙ Lg^* ⟶ L(g')^* ⋙ Rf'_*`. -/
theorem twistedInverseImagePushforwardBaseChange_eq_conjugateEquiv (sq : IsPullback g' f' f g) :
    twistedInverseImagePushforwardBaseChange g' f' f g hpushg' hpushf hpushf' hpushg sq =
      conjugateEquiv ((quasiCoherentDerivedAdjunction g' hpullg' hpushg').comp
          (twistedInverseImageAdjunction f' hpushf'))
        ((twistedInverseImageAdjunction f hpushf).comp
          (quasiCoherentDerivedAdjunction g hpullg hpushg))
        (quasiCoherentDerivedBaseChange g' f' f g hpushg' hpushf hpushf' hpushg hpullg hpullg'
          sq.w).natTrans := by
  rw [← iterated_mateEquiv_conjugateEquiv]
  exact (congrArg (fun γ => (mateEquiv (twistedInverseImageAdjunction f' hpushf')
    (twistedInverseImageAdjunction f hpushf) γ).natTrans)
      ((mateEquiv (quasiCoherentDerivedAdjunction g' hpullg' hpushg')
        (quasiCoherentDerivedAdjunction g hpullg hpushg)).apply_symm_apply _)).symm

/-- **`ξ` is invertible as soon as the base change map of derived direct image is.** This is the
proof of [Stacks, Tag 0A9K] from the invertibility of the base change map. -/
theorem isIso_twistedInverseImagePushforwardBaseChange_of_isIso (sq : IsPullback g' f' f g)
    [IsIso (quasiCoherentDerivedBaseChange g' f' f g hpushg' hpushf hpushf' hpushg hpullg hpullg'
      sq.w).natTrans] :
    IsIso (twistedInverseImagePushforwardBaseChange g' f' f g hpushg' hpushf hpushf' hpushg
      sq) := by
  rw [twistedInverseImagePushforwardBaseChange_eq_conjugateEquiv g' f' f g hpushg' hpushf
    hpushf' hpushg hpullg hpullg' sq]
  infer_instance

end Stacks.Duality
