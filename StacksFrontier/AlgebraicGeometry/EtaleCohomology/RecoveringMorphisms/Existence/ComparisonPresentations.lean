module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.Existence.RelativeSolutionPresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.Existence.PreimageOpen
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.BaseChangeSolutionPresentation

/-!
# The two rows of the comparison square, relative to an affine open of the target

Let `V` be an affine open of `Y` and `V'` an affine object of the small étale site of `Y` lying
over `V`, with a standard presentation `Γ(V', ⊤) ≅ Γ(V, ⊤)[x]/(P)`.

* On `Y_étale`, `V'` is a solution presentation relative to `V` with coefficients `Γ(V, ⊤)`
  (`AlgebraicGeometry.targetRelPresentation`): a chart over `V` maps to `V'` over `Y` exactly
  when it maps to `V'` over `V`, i.e. when it is a solution of `P`.
* On `X_étale`, for a morphism `g` of locally ringed topoi and the morphism of schemes
  `f : X ⟶ Y` glued from it, the base change `X ×_Y V'` is a solution presentation relative to
  `W_V = f⁻¹V` with coefficients pushed along `φ_V : Γ(V, ⊤) ⟶ Γ(W_V, ⊤)`
  (`AlgebraicGeometry.sourceRelPresentation`).

These are the two rows of the diagram in step (3) of the proof of Stacks 04I6, in the relative
form the global argument of Stacks 04I7 needs.

## References

* [Stacks Project, Tag 04I7](https://stacks.math.columbia.edu/tag/04I7)
* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits

universe u

namespace AlgebraicGeometry

/-- Over an open `V`, a morphism into an object lying over `V` is a morphism over `S` exactly
when it is one over `V`. -/
def overOpenEquiv {S U V' : Scheme.{u}} {V : S.Opens} (pV : V' ⟶ V.toScheme) (u : U ⟶ V.toScheme)
    (a : U ⟶ S) (ha : a = u ≫ V.ι) (b : V' ⟶ S) (hb : b = pV ≫ V.ι) :
    {m : U ⟶ V' // m ≫ b = a} ≃ {m : U ⟶ V' // m ≫ pV = u} :=
  Equiv.subtypeEquivRight fun m => by
    subst ha hb
    rw [← Category.assoc]
    exact cancel_mono V.ι

/-- The object of the small étale site given by an affine open is affine. -/
instance isAffine_openObj {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (V : S.affineOpens) :
    IsAffine ((SmallEtale.toScheme B S hS).obj (openObj B S hS (V : S.Opens))) :=
  V.2

/-- The solution of `P` read off a morphism over `Y'` depends only on the underlying
morphism. -/
theorem homOverEquivSolutions_congr {Y' U V : Scheme.{u}} [IsAffine Y'] [IsAffine V] {pV : V ⟶ Y'}
    {pU : U ⟶ Y'} {n : ℕ} {P : Fin n → MvPolynomial (Fin n) Γ(Y', ⊤)}
    (pres : Stacks.EtaleCohomology.StandardPresentationOver V pV P)
    {m m' : {m : U ⟶ V // m ≫ pV = pU}} (h : m.1 = m'.1) (i : Fin n) :
    (Stacks.EtaleCohomology.homOverEquivSolutions U V pV pU P pres m).1 i =
      (Stacks.EtaleCohomology.homOverEquivSolutions U V pV pU P pres m').1 i := by
  rw [Subtype.ext h]

section Target

variable {B : BigEtaleSite.{u}} {Y : B.Scheme} (V : Y.obj.affineOpens)
  {V' : SmallEtale B Y.obj Y.property} [IsAffine ((SmallEtale.toScheme B Y.obj Y.property).obj V')]
  (k : V' ⟶ openObj B Y.obj Y.property V) {n : ℕ}
  (P : Fin n → MvPolynomial (Fin n)
    Γ((SmallEtale.toScheme B Y.obj Y.property).obj (openObj B Y.obj Y.property V), ⊤))
  (pres : Stacks.EtaleCohomology.StandardPresentationOver
    ((SmallEtale.toScheme B Y.obj Y.property).obj V')
    ((SmallEtale.toScheme B Y.obj Y.property).map k) P)

/-- The structure map of an object of the small étale site lying over an open `W` factors
through `W`. -/
theorem smallEtaleMap_eq_comp {S : Scheme.{u}} {hS : B.Contains S} {U : SmallEtale B S hS}
    {W : S.Opens} (k : U ⟶ openObj B S hS W) :
    smallEtaleMap B S hS U = (SmallEtale.toScheme B S hS).map k ≫ W.ι :=
  (smallEtaleStructureHom_comp B S hS k).symm

/-- **The target row: `V'` as a solution presentation relative to `V`.** -/
def targetRelPresentation :
    RelSolutionPresentation B Y.obj Y.property V
      (RingHom.id Γ((SmallEtale.toScheme B Y.obj Y.property).obj (openObj B Y.obj Y.property V), ⊤))
      P where
  obj := V'
  over := k
  equiv U kU := ((smallEtaleHomEquivSchemeHomOver U V').trans
    (overOpenEquiv _ _ _ (smallEtaleMap_eq_comp kU) _ (smallEtaleMap_eq_comp k))).trans
      ((Stacks.EtaleCohomology.homOverEquivSolutions _ _ _
        ((SmallEtale.toScheme B Y.obj Y.property).map kU) P pres).trans
        (Equiv.subtypeEquivRight fun a => Iff.rfl))
  equiv_naturality {U U'} j kU f i := by
    change (pres.iso.inv ≫ ((SmallEtale.toScheme B Y.obj Y.property).map (j ≫ f)).appTop).hom
        (Ideal.Quotient.mk (Ideal.span (Set.range P)) (MvPolynomial.X i)) =
      smallEtaleRestrict B Y.obj Y.property j
        ((pres.iso.inv ≫ ((SmallEtale.toScheme B Y.obj Y.property).map f).appTop).hom
          (Ideal.Quotient.mk (Ideal.span (Set.range P)) (MvPolynomial.X i)))
    rw [Functor.map_comp, Scheme.Hom.comp_appTop]
    rfl

end Target

section Source

variable {B : BigEtaleSite.{u}} {X Y : B.Scheme}
  (g : RingedToposHom (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
  (V : Y.obj.affineOpens)
  {V' : SmallEtale B Y.obj Y.property} [IsAffine ((SmallEtale.toScheme B Y.obj Y.property).obj V')]
  (k : V' ⟶ openObj B Y.obj Y.property V) {n : ℕ}
  (P : Fin n → MvPolynomial (Fin n)
    Γ((SmallEtale.toScheme B Y.obj Y.property).obj (openObj B Y.obj Y.property V), ⊤))
  (pres : Stacks.EtaleCohomology.StandardPresentationOver
    ((SmallEtale.toScheme B Y.obj Y.property).obj V')
    ((SmallEtale.toScheme B Y.obj Y.property).map k) P)

/-- `φ_V`, with source and target spelled as global functions of objects of the small étale
sites. -/
def openRingHomObj (V : Y.obj.Opens) :
    ↥Γ((SmallEtale.toScheme B Y.obj Y.property).obj (openObj B Y.obj Y.property V), ⊤) →+*
      ↥Γ((SmallEtale.toScheme B X.obj X.property).obj
        (openObj B X.obj X.property (inverseImageOpen B X Y g V)), ⊤) :=
  openRingHom g V

/-- `AlgebraicGeometry.openRingHomObj` is `AlgebraicGeometry.openRingHom` on the nose. -/
theorem openRingHomObj_apply (V : Y.obj.Opens) (b) : openRingHomObj g V b = openRingHom g V b :=
  rfl

/-- The generalized element named by `φ_V b` is the one named by `b`, moved along `g`. -/
theorem smallEtaleSectionRingEquiv_symm_openRingHomObj (V : Y.obj.Opens) (b) :
    (smallEtaleSectionRingEquiv B X.obj X.property
      (openObj B X.obj X.property (inverseImageOpen B X Y g V))).symm (openRingHomObj g V b) =
      (inverseImageOpenIso g V).inv ≫ g.toToposHom.inverseImage.map
        ((smallEtaleSectionRingEquiv B Y.obj Y.property (openObj B Y.obj Y.property V)).symm b) ≫
          g.fSharpSet :=
  smallEtaleSectionRingEquiv_symm_openRingHom g V b

omit [IsAffine ((SmallEtale.toScheme B Y.obj Y.property).obj V')] in
/-- The base change `X ×_Y V'` lies over `W_V`. -/
theorem nonempty_baseChange_over (hg : g.IsLocallyRinged) (k : V' ⟶ openObj B Y.obj Y.property V) :
    Nonempty ((smallEtaleBaseChange B (glueHom g)).obj V' ⟶
      openObj B X.obj X.property (inverseImageOpen B X Y g V)) := by
  rw [nonempty_hom_opensToBoundedEtale_iff, ← preimage_glueHom_eq g hg V]
  rintro _ ⟨z, rfl⟩
  let U := (smallEtaleBaseChange B (glueHom g)).obj V'
  have hz := congrArg (fun m => m z) (baseChangeSchemeHom_comp (glueHom g) U V' (𝟙 U))
  simp only [Scheme.Hom.comp_apply] at hz
  show B.inclusion.map (glueHom g) (B.inclusion.map U.obj.hom z) ∈ (V : Y.obj.Opens)
  rw [← hz]
  exact (nonempty_hom_opensToBoundedEtale_iff B Y.obj Y.property V' V).1 ⟨k⟩ ⟨_, rfl⟩

/-- The structure map of a chart over `W_V`, followed by `f`, is the chart's map to `W_V`
followed by `f_V` and the inclusion of `V`. -/
theorem smallEtaleMap_comp_glueHom {U : SmallEtale B X.obj X.property}
    (kU : U ⟶ openObj B X.obj X.property (inverseImageOpen B X Y g V)) :
    B.inclusion.map U.obj.hom ≫ B.inclusion.map (glueHom g) =
      ((SmallEtale.toScheme B X.obj X.property).map kU ≫ openSchemeHom g V) ≫
        (V : Y.obj.Opens).ι := by
  rw [show B.inclusion.map U.obj.hom = smallEtaleMap B X.obj X.property U from rfl,
    smallEtaleMap_eq_comp kU]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (glueHom_spec g V)).trans
    (Category.assoc _ _ _).symm)

/-- Global functions of a morphism into `W_V` followed by `f_V`: the map on global functions is
`φ_V` followed by that of `m`. -/
theorem appTop_comp_openSchemeHom {T : Scheme.{u}}
    (m : T ⟶ (inverseImageOpen B X Y g V).toScheme) :
    (m ≫ openSchemeHom g V).appTop.hom = m.appTop.hom.comp (openRingHom g V) := by
  rw [Scheme.Hom.comp_appTop, openSchemeHom_appTop]
  rfl

/-- **The source row: `X ×_Y V'` as a solution presentation relative to `W_V`, with the
coefficients pushed along `φ_V`.** -/
def sourceRelPresentation (hg : g.IsLocallyRinged) :
    RelSolutionPresentation B X.obj X.property (inverseImageOpen B X Y g V)
      (openRingHomObj g V) P where
  obj := (smallEtaleBaseChange B (glueHom g)).obj V'
  over := Classical.choice (nonempty_baseChange_over g V hg k)
  equiv U kU := ((smallEtaleBaseChangeSchemeHomEquiv (glueHom g) U V').trans
    (overOpenEquiv _ _ _ (smallEtaleMap_comp_glueHom g V kU) _ (smallEtaleMap_eq_comp k))).trans
      ((Stacks.EtaleCohomology.homOverEquivSolutions _ _ _
        ((SmallEtale.toScheme B X.obj X.property).map kU ≫ openSchemeHom g V) P pres).trans
        (Equiv.subtypeEquivRight fun a => Iff.of_eq (congrArg
          (fun φ => MvPolynomial.IsSolution P φ a) (appTop_comp_openSchemeHom g V _))))
  equiv_naturality {U U'} j kU f i := by
    change (pres.iso.inv ≫ (baseChangeSchemeHom (glueHom g) U' V' (j ≫ f)).appTop).hom
        (Ideal.Quotient.mk (Ideal.span (Set.range P)) (MvPolynomial.X i)) =
      smallEtaleRestrict B X.obj X.property j
        ((pres.iso.inv ≫ (baseChangeSchemeHom (glueHom g) U V' f).appTop).hom
          (Ideal.Quotient.mk (Ideal.span (Set.range P)) (MvPolynomial.X i)))
    have h := smallEtaleBaseChangeSchemeHomEquiv_naturality (glueHom g) j V' f
    rw [smallEtaleBaseChangeSchemeHomEquiv_apply_coe,
      smallEtaleBaseChangeSchemeHomEquiv_apply_coe] at h
    rw [h, Scheme.Hom.comp_appTop]
    rfl

end Source

end AlgebraicGeometry

end
