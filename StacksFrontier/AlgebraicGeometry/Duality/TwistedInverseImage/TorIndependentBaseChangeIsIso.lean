module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.TorIndependentBaseChange
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonBaseChange
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.GlobalBaseChange
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TorIndependentBaseChange
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.AffineConservative
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.QcqsPushforwardAnyModel

/-!
# Tor independent base change on `D_QCoh` at the locally small model

For a cartesian square of schemes with `f` quasi-compact and quasi-separated and `X`, `S'` Tor
independent over `S`, the base change map `Lg^*Rf_*K ⟶ Rf'_*L(g')^*K` of the derived adjunctions
at the locally small model is invertible for `K` with quasi-coherent cohomology
([Stacks, Tag 08IB]).

## Main results

* `Stacks.Duality.isIso_quasiCoherentDerivedBaseChange` — the ambient base change map at
  `K ∈ D_QCoh(𝒪_X)` is invertible.
* `Stacks.Duality.isIso_quasiCoherentDerivedBaseChange_natTrans` — the base change transformation
  `Rf_* ⋙ Lg^* ⟶ L(g')^* ⋙ Rf'_*` on the quasi-coherent derived categories is invertible.
* `Stacks.Duality.isIso_quasiCoherentDerivedBaseChange_transpose` — the same for the transposed
  square, on `D_QCoh(𝒪_{S'})`.
* `Stacks.Duality.isIso_quasiCoherentTransposedUnitBaseChange` — the transposed base change map
  `Lf^*Rg_*𝟙' ⟶ Rg'_*𝟙''` at a unit is invertible.
* `Stacks.Duality.isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent` —
  [Stacks, Tag 0A9K].
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

/-- Two transports of derived pullback along the commutativity of a square of schemes agree. -/
theorem eqToIso_derivedPullback_inv_eq {X S : Scheme.{u}} {h₁ h₂ : X ⟶ S} (e : h₁ = h₂)
    (e' : h₂.toLRSHom.toShHom = h₁.toLRSHom.toShHom) :
    (eqToIso (congrArg (fun h => derivedPullback h) e)).inv =
      (StacksDraft.DerivedModel.derivedPullbackCongr e').hom := by
  subst e
  rfl

/-- If `T.inv = T'.hom`, then `A.hom ≫ (B ≪≫ T).inv = (A ≪≫ T').hom ≫ B.inv`. -/
theorem hom_comp_trans_inv_eq {C D : Type*} [Category C] [Category D] {F₁ F₂ G₁ G₂ : C ⥤ D}
    (A : F₁ ≅ G₁) (B : F₂ ≅ G₂) (T : G₂ ≅ G₁) (T' : G₁ ≅ G₂) (h : T.inv = T'.hom) :
    A.hom ≫ (B ≪≫ T).inv = (A ≪≫ T').hom ≫ B.inv := by
  simp [h]

variable {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}

/-- **The base change map of the derived adjunctions at the locally small model is invertible at
`K` when the derived base change map of [Stacks, Tag 08HY] at the standard model is.** -/
theorem isIso_quasiCoherentDerivedBaseChange_of_standard (sq : g' ≫ f = f' ≫ g)
    (K : quasiCoherentDerivedCategory X)
    (h : IsIso (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g'.toLRSHom.toShHom
      f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom (comp_toShHom_of_comm sq)
      (K.obj : @DerivedCategory _ _ _ (HasDerivedCategory.standard
        (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)))))) :
    IsIso (Stacks.CategoryTheory.BaseChange.map (derivedAdjunction f) (derivedAdjunction f')
      (derivedPullbackCompIso f' g)
      (derivedPullbackCompIso g' f ≪≫ eqToIso (congrArg (fun h => derivedPullback h) sq))
      K.obj) := by
  have h' := StacksDraft.DerivedModel.isIso_baseChangeMap_of_isIso_derivedBaseChangeMap _ _ _ _
    (comp_toShHom_of_comm sq) _ h
  have heq : (derivedPullbackCompIso f' g).hom ≫
      (derivedPullbackCompIso g' f ≪≫ eqToIso (congrArg (fun h => derivedPullback h) sq)).inv =
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f'.toLRSHom.toShHom
          g.toLRSHom.toShHom ≪≫
        StacksDraft.DerivedModel.derivedPullbackCongr (comp_toShHom_of_comm sq).symm).hom ≫
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g'.toLRSHom.toShHom
          f.toLRSHom.toShHom).inv :=
    hom_comp_trans_inv_eq _ _ _ _ (eqToIso_derivedPullback_inv_eq sq _)
  rw [Stacks.CategoryTheory.BaseChange.map_eq_of_hom_comp_inv_eq _ _ _ _ _ _ heq K.obj]
  exact h'

/-- **Tor independent base change at the locally small model.** For a cartesian square with `f`
quasi-compact and quasi-separated and `X`, `S'` Tor independent over `S`, the base change map
`Lg^*Rf_*K ⟶ Rf'_*L(g')^*K` of the derived adjunctions is invertible for every `K` in
`D_QCoh(𝒪_X)` ([Stacks, Tag 08IB]). -/
theorem isIso_quasiCoherentDerivedBaseChange (sq : IsPullback g' f' f g) [QuasiCompact f]
    [QuasiSeparated f] (hTor : TorIndependent f g) (K : quasiCoherentDerivedCategory X) :
    IsIso (Stacks.CategoryTheory.BaseChange.map (derivedAdjunction f) (derivedAdjunction f')
      (derivedPullbackCompIso f' g)
      (derivedPullbackCompIso g' f ≪≫ eqToIso (congrArg (fun h => derivedPullback h) sq.w))
      K.obj) :=
  isIso_quasiCoherentDerivedBaseChange_of_standard sq.w K
    (isIso_derivedBaseChangeMap_of_torIndependent sq hTor K.obj fun n =>
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
        ((homologyFunctorModelIso _ n).app K.obj) (K.property n))

/-- `isIso_quasiCoherentDerivedBaseChange` over affine schemes `S` and `S'`. -/
theorem isIso_quasiCoherentDerivedBaseChange_of_isAffine (sq : IsPullback g' f' f g)
    [IsAffine S] [IsAffine S'] [QuasiCompact f] [QuasiSeparated f] (hTor : TorIndependent f g)
    (K : quasiCoherentDerivedCategory X) :
    IsIso (Stacks.CategoryTheory.BaseChange.map (derivedAdjunction f) (derivedAdjunction f')
      (derivedPullbackCompIso f' g)
      (derivedPullbackCompIso g' f ≪≫ eqToIso (congrArg (fun h => derivedPullback h) sq.w))
      K.obj) :=
  isIso_quasiCoherentDerivedBaseChange sq hTor K

end Stacks.Duality

end

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

variable {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}

/-- The comparison of the composite derived pullbacks with the transport written as an inverse. -/
private theorem derivedPullbackCompIso_hom_comp_eqToHom_eq (w : g' ≫ f = f' ≫ g) :
    (derivedPullbackCompIso f' g).hom ≫
        eqToHom (congrArg (fun h : X' ⟶ S => derivedPullback h) w.symm) ≫
          (derivedPullbackCompIso g' f).inv =
      (derivedPullbackCompIso f' g).hom ≫
        (derivedPullbackCompIso g' f ≪≫ eqToIso (congrArg (fun h => derivedPullback h) w)).inv := by
  rw [Iso.trans_inv, eqToIso.inv]

/-- The comparison of the composite derived pullbacks on `D_QCoh` has the ambient components. -/
private theorem quasiCoherentDerivedPullbackCompIso_hom_comp_inv_app_hom (w : g' ≫ f = f' ≫ g)
    (K : quasiCoherentDerivedCategory S) :
    (((quasiCoherentDerivedPullbackCompIso f' g).hom ≫
      (quasiCoherentDerivedPullbackCompIso g' f ≪≫ quasiCoherentDerivedPullbackCongr w).inv).app
        K).hom =
      ((derivedPullbackCompIso f' g).hom ≫
        (derivedPullbackCompIso g' f ≪≫ eqToIso (congrArg (fun h => derivedPullback h) w)).inv).app
          K.obj :=
  (squareCompositeIso_quasiCoherentDerivedPullbackCompIso_hom_app_hom g' f' f g w K).trans
    (congrArg (fun t => NatTrans.app t K.obj) (derivedPullbackCompIso_hom_comp_eqToHom_eq w))

end Stacks.Duality

end

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

variable {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
  (hpushg' : ∀ (K : quasiCoherentDerivedCategory X') (i : ℤ),
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((derivedPushforward g').obj K.obj)).IsQuasicoherent)
  (hpushf : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor S.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
  (hpushf' : ∀ (K : quasiCoherentDerivedCategory X') (i : ℤ),
    ((DerivedCategory.homologyFunctor S'.Modules i).obj
      ((derivedPushforward f').obj K.obj)).IsQuasicoherent)
  (hpushg : ∀ (K : quasiCoherentDerivedCategory S') (i : ℤ),
    ((DerivedCategory.homologyFunctor S.Modules i).obj
      ((derivedPushforward g).obj K.obj)).IsQuasicoherent)

/-- **The base change map on `D_QCoh` is invertible at `K` when the ambient one is**: its
underlying morphism is the ambient base change map. -/
theorem isIso_quasiCoherentDerivedBaseChange_app_of_isIso (w : g' ≫ f = f' ≫ g)
    (K : quasiCoherentDerivedCategory X)
    [hK : IsIso (Stacks.CategoryTheory.BaseChange.map (derivedAdjunction f) (derivedAdjunction f')
      (derivedPullbackCompIso f' g)
      (derivedPullbackCompIso g' f ≪≫ eqToIso (congrArg (fun h => derivedPullback h) w))
      K.obj)] :
    IsIso ((quasiCoherentDerivedBaseChange g' f' f g hpushg' hpushf hpushf' hpushg
      (isQuasicoherent_homology_derivedPullback' g) (isQuasicoherent_homology_derivedPullback' g')
      w).natTrans.app K) := by
  rw [quasiCoherentDerivedBaseChange_eq_twoSquare]
  have e := ObjectProperty.map_restrictFullyFaithful_hom (derivedAdjunction f)
    (derivedAdjunction f') (isQuasicoherent_homology_derivedPullback' f) hpushf
    (isQuasicoherent_homology_derivedPullback' f') hpushf'
    (isQuasicoherent_homology_derivedPullback' g) (isQuasicoherent_homology_derivedPullback' g')
    (derivedPullbackCompIso f' g)
    (derivedPullbackCompIso g' f ≪≫ eqToIso (congrArg (fun h => derivedPullback h) w))
    (quasiCoherentDerivedPullbackCompIso f' g)
    (quasiCoherentDerivedPullbackCompIso g' f ≪≫ quasiCoherentDerivedPullbackCongr w)
    (quasiCoherentDerivedPullbackCompIso_hom_comp_inv_app_hom w) K
  rw [← e] at hK
  exact @Functor.FullyFaithful.isIso_of_isIso_map _ _ _ _ _ (ObjectProperty.fullyFaithfulι _) _ _ _
    hK

/-- **Tor independent base change on `D_QCoh`**: for a cartesian square with `f` quasi-compact
and quasi-separated and `X`, `S'` Tor independent over `S`, the base change transformation
`Rf_* ⋙ Lg^* ⟶ L(g')^* ⋙ Rf'_*` of the quasi-coherent derived categories is invertible. -/
theorem isIso_quasiCoherentDerivedBaseChange_natTrans (sq : IsPullback g' f' f g)
    [QuasiCompact f] [QuasiSeparated f] (hTor : TorIndependent f g) :
    IsIso (quasiCoherentDerivedBaseChange g' f' f g hpushg' hpushf hpushf' hpushg
      (isQuasicoherent_homology_derivedPullback' g) (isQuasicoherent_homology_derivedPullback' g')
      sq.w).natTrans := by
  have : ∀ K, IsIso ((quasiCoherentDerivedBaseChange g' f' f g hpushg' hpushf hpushf' hpushg
      (isQuasicoherent_homology_derivedPullback' g) (isQuasicoherent_homology_derivedPullback' g')
      sq.w).natTrans.app K) := fun K => by
    have := isIso_quasiCoherentDerivedBaseChange sq hTor K
    exact isIso_quasiCoherentDerivedBaseChange_app_of_isIso hpushg' hpushf hpushf' hpushg sq.w K
  exact NatIso.isIso_of_isIso_app _

end Stacks.Duality

end

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

variable {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}

/-- The comparison of the composite derived pullbacks on `D_QCoh` read across the transposed
square has the ambient components. -/
private theorem quasiCoherentDerivedPullbackCompIso_congr_hom_comp_inv_app_hom
    (w : g' ≫ f = f' ≫ g) (w' : f' ≫ g = g' ≫ f) (K : quasiCoherentDerivedCategory S) :
    (((quasiCoherentDerivedPullbackCompIso g' f ≪≫ quasiCoherentDerivedPullbackCongr w).hom ≫
      (quasiCoherentDerivedPullbackCompIso f' g).inv).app K).hom =
      ((derivedPullbackCompIso g' f).hom ≫
        (derivedPullbackCompIso f' g ≪≫
          eqToIso (congrArg (fun h => derivedPullback h) w')).inv).app K.obj := by
  have e : ((derivedPullbackCompIso g' f).hom ≫
      (derivedPullbackCompIso f' g ≪≫
        eqToIso (congrArg (fun h => derivedPullback h) w')).inv).app K.obj =
      (derivedPullbackCompIso g' f).hom.app K.obj ≫
        eqToHom (congrArg (fun h : X' ⟶ S => (derivedPullback h).obj K.obj) w'.symm) ≫
          (derivedPullbackCompIso f' g).inv.app K.obj := by
    rw [Iso.trans_inv, eqToIso.inv, NatTrans.comp_app, NatTrans.comp_app, eqToHom_app]
  rw [e, NatTrans.comp_app, Iso.trans_hom, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    quasiCoherentDerivedPullbackCompIso_hom_app_hom,
    quasiCoherentDerivedPullbackCompIso_inv_app_hom, Category.assoc]
  rfl

end Stacks.Duality

end

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

variable {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
  (hpushg' : ∀ (K : quasiCoherentDerivedCategory X') (i : ℤ),
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((derivedPushforward g').obj K.obj)).IsQuasicoherent)
  (hpushg : ∀ (K : quasiCoherentDerivedCategory S') (i : ℤ),
    ((DerivedCategory.homologyFunctor S.Modules i).obj
      ((derivedPushforward g).obj K.obj)).IsQuasicoherent)

/-- **Tor independent base change on `D_QCoh` across the transposed square**: for a cartesian
square with `g` quasi-compact and quasi-separated and `X`, `S'` Tor independent over `S`, the base
change map `Lf^*Rg_*K ⟶ Rg'_*L(f')^*K` of the adjunctions `Lg^* ⊣ Rg_*` and `L(g')^* ⊣ Rg'_*` on
the quasi-coherent derived categories is invertible for every `K` in `D_QCoh(𝒪_{S'})`
([Stacks, Tag 08IB] for the transposed square). -/
theorem isIso_quasiCoherentDerivedBaseChange_transpose (sq : IsPullback g' f' f g)
    [QuasiCompact g] [QuasiSeparated g] (hTor : TorIndependent f g)
    (K : quasiCoherentDerivedCategory S') :
    IsIso (Stacks.CategoryTheory.BaseChange.map
      (quasiCoherentDerivedAdjunction g (isQuasicoherent_homology_derivedPullback' g) hpushg)
      (quasiCoherentDerivedAdjunction g' (isQuasicoherent_homology_derivedPullback' g') hpushg')
      (quasiCoherentDerivedPullbackCompIso g' f ≪≫ quasiCoherentDerivedPullbackCongr sq.w)
      (quasiCoherentDerivedPullbackCompIso f' g) K) := by
  have hK := isIso_quasiCoherentDerivedBaseChange sq.flip hTor.symm K
  have e := ObjectProperty.map_restrictFullyFaithful_hom (derivedAdjunction g)
    (derivedAdjunction g') (isQuasicoherent_homology_derivedPullback' g) hpushg
    (isQuasicoherent_homology_derivedPullback' g') hpushg'
    (isQuasicoherent_homology_derivedPullback' f) (isQuasicoherent_homology_derivedPullback' f')
    (derivedPullbackCompIso g' f)
    (derivedPullbackCompIso f' g ≪≫ eqToIso (congrArg (fun h => derivedPullback h) sq.flip.w))
    (quasiCoherentDerivedPullbackCompIso g' f ≪≫ quasiCoherentDerivedPullbackCongr sq.w)
    (quasiCoherentDerivedPullbackCompIso f' g)
    (quasiCoherentDerivedPullbackCompIso_congr_hom_comp_inv_app_hom sq.w sq.flip.w) K
  rw [← e] at hK
  exact @Functor.FullyFaithful.isIso_of_isIso_map _ _ _ _ _ (ObjectProperty.fullyFaithfulι _) _ _ _
    hK

/-- **The transposed base change map at a unit is invertible** on `D_QCoh`: for a cartesian
square with `g` quasi-compact and quasi-separated and `X`, `S'` Tor independent over `S`, and an
isomorphism `u : L(f')^*𝟙' ⟶ 𝟙''`, the map `τ : Lf^*Rg_*𝟙' ⟶ Rg'_*L(f')^*𝟙' ⟶ Rg'_*𝟙''` of
`Stacks.CategoryTheory.BaseChange.transposedUnitBaseChange` is invertible. -/
theorem isIso_quasiCoherentTransposedUnitBaseChange (sq : IsPullback g' f' f g)
    [QuasiCompact g] [QuasiSeparated g] (hTor : TorIndependent f g)
    (o' : quasiCoherentDerivedCategory S') (o'' : quasiCoherentDerivedCategory X')
    (u : (quasiCoherentDerivedPullback' f').obj o' ⟶ o'') [IsIso u] :
    IsIso (Stacks.CategoryTheory.BaseChange.transposedUnitBaseChange
      (quasiCoherentDerivedAdjunction g (isQuasicoherent_homology_derivedPullback' g) hpushg)
      (quasiCoherentDerivedAdjunction g' (isQuasicoherent_homology_derivedPullback' g') hpushg')
      (quasiCoherentDerivedPullbackCompIso f' g)
      (quasiCoherentDerivedPullbackCompIso g' f ≪≫ quasiCoherentDerivedPullbackCongr sq.w)
      o' o'' u) := by
  have := isIso_quasiCoherentDerivedBaseChange_transpose hpushg' hpushg sq hTor o'
  unfold Stacks.CategoryTheory.BaseChange.transposedUnitBaseChange
  infer_instance

end Stacks.Duality

end

/-! ### [Stacks, Tag 0A9K] -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

/-- **[Stacks, Tag 0A9K].** Let
```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```
be a cartesian square of quasi-compact and quasi-separated schemes (Situation [Stacks, Tag 0A9J]:
all four schemes), and let `a`, `a'` be the right adjoints of `Rf_*`, `Rf'_*` on `D_QCoh`
([Stacks, Tag 0A9E]). If `f` and `g` are Tor independent (for instance if `g` is flat,
`AlgebraicGeometry.torIndependent_of_flat_right`), the transformation
`ξ : Rg'_* ∘ a' ⟶ a ∘ Rg_*` is invertible. -/
@[stacks 0A9K]
theorem isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent
    {X' X Y' Y : Scheme.{u}} [CompactSpace X'] [QuasiSeparatedSpace X'] [CompactSpace X]
    [QuasiSeparatedSpace X] [CompactSpace Y'] [QuasiSeparatedSpace Y'] [CompactSpace Y]
    [QuasiSeparatedSpace Y] {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) (hTor : TorIndependent f g) :
    IsIso (twistedInverseImagePushforwardBaseChange g' f' f g
      (isQuasicoherent_homology_derivedPushforward_of_qcqs g')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs g) sq) := by
  have := isIso_quasiCoherentDerivedBaseChange_natTrans
    (isQuasicoherent_homology_derivedPushforward_of_qcqs g')
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
    (isQuasicoherent_homology_derivedPushforward_of_qcqs g) sq hTor
  exact isIso_twistedInverseImagePushforwardBaseChange_of_isIso g' f' f g _ _ _ _
    (isQuasicoherent_homology_derivedPullback' g) (isQuasicoherent_homology_derivedPullback' g') sq

end Stacks.Duality
