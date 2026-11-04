module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedOverSpace.PointProducts
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedOverSpace.InverseImageComparison
public import StacksFrontier.CategoryTheory.Bicategory.CoGrothendieckInverseImageDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FullnessViaSigmaSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.EtaleComparisonRepresentable

/-!
# The functor `F^R` of Stacks 0E94 is full

Let `η : F^R(X, L) ⟶ F^R(X', L')` be a morphism of the functors over the site attached by `F^R`
to two polarized families of algebraic spaces over `T`. Its underlying isomorphism `f : X ≅ X'`
over `T` comes from Stacks 0E93 (`AlgebraicGeometry.PolarizedOverSpace.fullBaseMap`). On the
base change `Z₀ ⟶ X` of an étale atlas `U₀ ⟶ T` the component of `η` is a morphism
`ψ : q₀^* L ⟶ q₀^* f^* L'` (`CategoryTheory.Pseudofunctor.CoGrothendieck.descentFiber`), which
satisfies the pairwise condition of Stacks 04W3 on `Z₀ ×_X Z₀` because `η` is natural for the
two projections of the product point `U₀ ×_T U₀` and the base change along that point is
`Z₀ ×_X Z₀` (`AlgebraicGeometry.PolarizedOverSpace.isPullback_fibreMap_prodPoint`). Since
`Z₀ ⟶ X` is an étale covering (Stacks 041F), the fullness half of Stacks 04W6 gives a morphism
`φ : L ⟶ f^* L'` with `q₀^* φ = ψ`; it is invertible because its inverse descends the same way.
Then `(f, φ)` is an isomorphism of polarized families whose image under `F^R` is `η`: on every
point `a` of `T`, the inverse image along `Z_{a ×_T U₀} ⟶ Z_a`, which is an étale covering, is
injective on morphisms.

All coherences of inverse images are those of an abstract pseudofunctor, proved in
`StacksFrontier/CategoryTheory/Bicategory/CoGrothendieckInverseImageDescent.lean`; the passage to
inverse images of modules (Stacks 03LU) and to the comparisons of Stacks 04W5 is made one
morphism at a time.

## Main results

* `AlgebraicGeometry.PolarizedOverSpace.fullTheta`: `η` as a natural transformation of the
  families of inverse images, to which the coherences of
  `StacksFrontier/CategoryTheory/Bicategory/CoGrothendieckInverseImageDescent.lean` apply.
* `AlgebraicGeometry.PolarizedOverSpace.modulePullback_compat_of_modulesPseudofunctor`: the
  pairwise condition in the pseudofunctor of modules is the pairwise condition of Stacks 04W3.
* `AlgebraicGeometry.PolarizedOverSpace.prodPointPairMap`: the base change along `U₀ ×_T U₀` is
  `Z₀ ×_X Z₀`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Pseudofunctor.CoGrothendieck

universe u

/-- Two functors intertwined by a morphism and two given morphisms are intertwined by its
inverse, the other way round. -/
theorem CategoryTheory.Functor.map_inv_comp_eq_comp_map_inv {C D : Type*} [Category C]
    [Category D] (P₁ P₂ : C ⥤ D) {X Y : C} {cX : P₁.obj X ⟶ P₂.obj X} {cY : P₁.obj Y ⟶ P₂.obj Y}
    (w : X ⟶ Y) [IsIso w] (h : P₁.map w ≫ cY = cX ≫ P₂.map w) :
    P₁.map (CategoryTheory.inv w) ≫ cX = cY ≫ P₂.map (CategoryTheory.inv w) := by
  have e := congrArg (fun t => P₁.map (CategoryTheory.inv w) ≫ t ≫ P₂.map (CategoryTheory.inv w)) h
  simp only [Category.assoc, ← P₂.map_comp, IsIso.hom_inv_id, P₂.map_id, Category.comp_id,
    ← P₁.map_comp_assoc, IsIso.inv_hom_id, P₁.map_id, Category.id_comp] at e
  exact e.symm

namespace AlgebraicGeometry.PolarizedOverSpace

attribute [local implicit_reducible] Stack.fibredCategory BasedCategory.ofFunctor schemeSpace
  Functor.toPseudofunctor' pseudofunctorOfIsLocallyDiscrete typeToGrpd Grpd.forgetToCat
  MorphismProperty

variable {B : BigFppfSite.{u}}

section Crossing

-- Elaboration compares the inverse images of the pseudofunctor with the functors themselves
-- without unfolding the latter.
attribute [local irreducible] Space.modulePullback Space.modulePullbackCompIso

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **The pairwise condition read in the pseudofunctor of modules is the pairwise condition of
Stacks 04W3**, read through the comparisons of Stacks 04W5. -/
theorem modulePullback_compat_of_modulesPseudofunctor
    {X Y₀ P : AlgebraicSpaces B integerBase (hZ B)} (s₀ : Y₀ ⟶ X) (p₁ p₂ : P ⟶ Y₀)
    (hp : p₁ ≫ s₀ = p₂ ≫ s₀) (k : P ⟶ X) (hk₁ : p₁ ≫ s₀ = k) (hk₂ : p₂ ≫ s₀ = k)
    (hF₁ : s₀.op.toLoc ≫ p₁.op.toLoc = k.op.toLoc)
    (hF₂ : s₀.op.toLoc ≫ p₂.op.toLoc = k.op.toLoc)
    {M N : (Space.modulesPseudofunctor B integerBase (hZ B)).obj ⟨op X⟩}
    (w : ((Space.modulesPseudofunctor B integerBase (hZ B)).map s₀.op.toLoc).toFunctor.obj M ⟶
      ((Space.modulesPseudofunctor B integerBase (hZ B)).map s₀.op.toLoc).toFunctor.obj N)
    (H : ((Space.modulesPseudofunctor B integerBase (hZ B)).map p₁.op.toLoc).toFunctor.map w ≫
        ((Space.modulesPseudofunctor B integerBase (hZ B)).mapComp' s₀.op.toLoc p₁.op.toLoc
          k.op.toLoc hF₁).inv.toNatTrans.app N ≫
        ((Space.modulesPseudofunctor B integerBase (hZ B)).mapComp' s₀.op.toLoc p₂.op.toLoc
          k.op.toLoc hF₂).hom.toNatTrans.app N =
      ((Space.modulesPseudofunctor B integerBase (hZ B)).mapComp' s₀.op.toLoc p₁.op.toLoc
          k.op.toLoc hF₁).inv.toNatTrans.app M ≫
        ((Space.modulesPseudofunctor B integerBase (hZ B)).mapComp' s₀.op.toLoc p₂.op.toLoc
          k.op.toLoc hF₂).hom.toNatTrans.app M ≫
        ((Space.modulesPseudofunctor B integerBase (hZ B)).map p₂.op.toLoc).toFunctor.map w) :
    (Space.modulePullback B integerBase (hZ B) p₁).map w ≫
        (Space.QuasiCoherentDescent.canonicalComparison p₁ p₂ s₀ s₀ hp N).hom =
      (Space.QuasiCoherentDescent.canonicalComparison p₁ p₂ s₀ s₀ hp M).hom ≫
        (Space.modulePullback B integerBase (hZ B) p₂).map w := by
  have e : ∀ L : Space.Modules.{u, u} B integerBase (hZ B) X.1 X.2,
      (Space.QuasiCoherentDescent.canonicalComparison p₁ p₂ s₀ s₀ hp L).hom =
        (Space.QuasiCoherentDescent.pullbackComparison B integerBase (hZ B) p₁ s₀ k hk₁ L).inv ≫
          (Space.QuasiCoherentDescent.pullbackComparison B integerBase (hZ B) p₂ s₀ k hk₂ L).hom :=
    fun L => (congrArg Iso.hom
      (Space.QuasiCoherentDescent.canonicalComparison_eq_pullbackComparison B integerBase (hZ B)
        p₁ p₂ s₀ s₀ hp k hk₁ hk₂ L)).trans
      ((Iso.trans_hom _ _).trans (congrArg (· ≫ _) (Iso.symm_hom _)))
  simp only [Space.modulesPseudofunctor_mapComp'_inv_app p₁ s₀ k hk₁ hF₁,
    Space.modulesPseudofunctor_mapComp'_hom_app p₂ s₀ k hk₂ hF₂] at H
  rw [e N, e M, Category.assoc]
  erw [← modulesPseudofunctor_map_map p₁ w, ← modulesPseudofunctor_map_map p₂ w]
  exact H

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **The pairwise condition of Stacks 04W3 for a single-member family, from the pairwise
condition read in the pseudofunctor of modules.** The member `Yi ()`, its morphism `fi ()`, the
fibre product `Yi () ×_X Yi ()` with its projections and the morphism `wi ()` are given a second
time as `Y₀`, `s₀`, `P`, `p₁`, `p₂` and `w`, in the form in which the pairwise condition `H` is
stated, together with the equalities identifying the two. The identification is made here, at
variable level, by substitution, so that `H` and the conclusion can each be instantiated in their
own form. -/
theorem isPairwiseCompatible_unit_of_modulesPseudofunctor {X : AlgebraicSpaces B integerBase (hZ B)}
    (Yi : Unit → AlgebraicSpaces B integerBase (hZ B)) (fi : ∀ i, Yi i ⟶ X)
    {M N : (Space.modulesPseudofunctor B integerBase (hZ B)).obj ⟨op X⟩}
    (wi : ∀ i, (Space.modulePullback B integerBase (hZ B) (fi i)).obj M ⟶
      (Space.modulePullback B integerBase (hZ B) (fi i)).obj N)
    {Y₀ P : AlgebraicSpaces B integerBase (hZ B)} {s₀ : Y₀ ⟶ X} {p₁ p₂ : P ⟶ Y₀} {k : P ⟶ X}
    (hk₁ : p₁ ≫ s₀ = k) (hk₂ : p₂ ≫ s₀ = k) {hF₁ : s₀.op.toLoc ≫ p₁.op.toLoc = k.op.toLoc}
    {hF₂ : s₀.op.toLoc ≫ p₂.op.toLoc = k.op.toLoc}
    {w : ((Space.modulesPseudofunctor B integerBase (hZ B)).map s₀.op.toLoc).toFunctor.obj M ⟶
      ((Space.modulesPseudofunctor B integerBase (hZ B)).map s₀.op.toLoc).toFunctor.obj N}
    (hY : Yi () = Y₀) (hP : Space.QuasiCoherentDescent.pair B integerBase (hZ B) Yi fi () () = P)
    (hs : HEq (fi ()) s₀)
    (hp₁ : HEq (Space.QuasiCoherentDescent.pairFst B integerBase (hZ B) Yi fi () ()) p₁)
    (hp₂ : HEq (Space.QuasiCoherentDescent.pairSnd B integerBase (hZ B) Yi fi () ()) p₂)
    (hw : HEq (wi ()) w)
    (H : ((Space.modulesPseudofunctor B integerBase (hZ B)).map p₁.op.toLoc).toFunctor.map w ≫
        ((Space.modulesPseudofunctor B integerBase (hZ B)).mapComp' s₀.op.toLoc p₁.op.toLoc
          k.op.toLoc hF₁).inv.toNatTrans.app N ≫
        ((Space.modulesPseudofunctor B integerBase (hZ B)).mapComp' s₀.op.toLoc p₂.op.toLoc
          k.op.toLoc hF₂).hom.toNatTrans.app N =
      ((Space.modulesPseudofunctor B integerBase (hZ B)).mapComp' s₀.op.toLoc p₁.op.toLoc
          k.op.toLoc hF₁).inv.toNatTrans.app M ≫
        ((Space.modulesPseudofunctor B integerBase (hZ B)).mapComp' s₀.op.toLoc p₂.op.toLoc
          k.op.toLoc hF₂).hom.toNatTrans.app M ≫
        ((Space.modulesPseudofunctor B integerBase (hZ B)).map p₂.op.toLoc).toFunctor.map w) :
    Space.QuasiCoherentDescent.IsPairwiseCompatible B integerBase (hZ B) Yi fi wi := by
  subst hY hP
  obtain rfl := eq_of_heq hs
  obtain rfl := eq_of_heq hp₁
  obtain rfl := eq_of_heq hp₂
  obtain rfl := eq_of_heq hw
  -- The comparison proof is passed literally, so that it is the one of the pairwise condition.
  have C := modulePullback_compat_of_modulesPseudofunctor (fi ()) _ _
    (Space.QuasiCoherentDescent.pair_condition B integerBase (hZ B) Yi fi () ()) k hk₁ hk₂ hF₁ hF₂
    (wi ()) H
  -- The same equation, with the morphisms typed in the category of modules.
  have C₂ : (Space.modulePullback B integerBase (hZ B)
        (Space.QuasiCoherentDescent.pairFst B integerBase (hZ B) Yi fi () ())).map (wi ()) ≫
      (Space.QuasiCoherentDescent.canonicalComparison
        (Space.QuasiCoherentDescent.pairFst B integerBase (hZ B) Yi fi () ())
        (Space.QuasiCoherentDescent.pairSnd B integerBase (hZ B) Yi fi () ()) (fi ()) (fi ())
        (Space.QuasiCoherentDescent.pair_condition B integerBase (hZ B) Yi fi () ()) N).hom =
      (Space.QuasiCoherentDescent.canonicalComparison
        (Space.QuasiCoherentDescent.pairFst B integerBase (hZ B) Yi fi () ())
        (Space.QuasiCoherentDescent.pairSnd B integerBase (hZ B) Yi fi () ()) (fi ()) (fi ())
        (Space.QuasiCoherentDescent.pair_condition B integerBase (hZ B) Yi fi () ()) M).hom ≫
      (Space.modulePullback B integerBase (hZ B)
        (Space.QuasiCoherentDescent.pairSnd B integerBase (hZ B) Yi fi () ())).map (wi ()) := C
  intro i j
  obtain rfl : i = () := rfl
  obtain rfl : j = () := rfl
  exact C₂

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Injectivity on morphisms of the inverse image along `g`, read in the pseudofunctor of
modules. The two languages are compared here at variable modules only. -/
theorem modulesPseudofunctor_map_injective {X Y : AlgebraicSpaces B integerBase (hZ B)}
    (g : X ⟶ Y)
    (hinj : ∀ {M N : Space.Modules.{u, u} B integerBase (hZ B) Y.1 Y.2} (a b : M ⟶ N),
      (Space.modulePullback B integerBase (hZ B) g).map a =
        (Space.modulePullback B integerBase (hZ B) g).map b → a = b)
    {M N : (Space.modulesPseudofunctor B integerBase (hZ B)).obj ⟨op Y⟩} (a b : M ⟶ N)
    (h : ((Space.modulesPseudofunctor B integerBase (hZ B)).map g.op.toLoc).toFunctor.map a =
      ((Space.modulesPseudofunctor B integerBase (hZ B)).map g.op.toLoc).toFunctor.map b) :
    a = b :=
  hinj a b ((modulesPseudofunctor_map_map g a).symm.trans
    (h.trans (modulesPseudofunctor_map_map g b)))

end Crossing

/-- The base change of a single-member étale covering along a cartesian square is a
single-member étale covering (Stacks 041F). -/
theorem isEtaleCovering_fst_of_isPullback
    {P Y Z X : (BigFppfOver B integerBase (hZ B))ᵒᵖ ⥤ Type u} {fst : P ⟶ Y} {snd : P ⟶ Z}
    {f : Y ⟶ X} {g : Z ⟶ X} (sq : IsPullback fst snd f g)
    (hY : IsAlgebraicSpace B integerBase (hZ B) Y)
    (hg : Space.IsEtaleCovering B integerBase (hZ B) (fun _ : Unit => Z) (fun _ => g)) :
    Space.IsEtaleCovering B integerBase (hZ B) (fun _ : Unit => P) (fun _ => fst) := by
  have h₁ := Space.isEtaleCovering_pullback B integerBase (hZ B) f hY _ _ hg
  have h₂ := Space.isEtaleCovering_comp B integerBase (hZ B) (fun _ : Unit => Unit) _ _ _
    (fun _ _ => sq.isoPullback.hom) h₁
    (fun _ => Space.isEtaleCovering_of_isIso B integerBase (hZ B) _
      (h₁.source_isAlgebraicSpace ()))
  have h₃ := Space.IsEtaleCovering.reindex B integerBase (hZ B) h₂
    (σ := fun _ : Unit => (⟨(), ()⟩ : Σ _ : Unit, Unit))
    (fun x => ⟨(), by obtain ⟨⟨⟩, ⟨⟩⟩ := x; rfl⟩)
  have e : (fun _ : Unit => sq.isoPullback.hom ≫ pullback.fst f g) = fun _ => fst :=
    funext fun _ => IsPullback.isoPullback_hom_fst _
  exact (congrArg (Space.IsEtaleCovering B integerBase (hZ B) (fun _ : Unit => P)) e).mp h₃

variable {T : AlgebraicSpaces B integerBase (hZ B)}

/-- The base change of a polarized family along a point is relatively representable over the
total space. -/
theorem relativelyRepresentable_fibreFst (ξ : PolarizedSpacesOver B T) (a : (Points T).obj) :
    yoneda.relativelyRepresentable (fibreFst ξ a) :=
  MorphismProperty.of_isPullback (isPullback_fibre ξ a).flip (relativelyRepresentable_pointMap a)

/-- **Inverse images along the base change `Z_{a ×_T U₀} ⟶ Z_a` of the atlas are injective on
morphisms**, that base change being an étale covering. -/
theorem modulePullback_fibreMap_prodPointFst_injective (ξ : PolarizedSpacesOver B T)
    (a : (Points T).obj)
    {M N : Space.Modules B integerBase (hZ B) (yoneda.obj (fibreScheme ξ a))
      ((arrowSpace B).obj ((fibreArrowFunctor ξ).obj a)).property} (φ ψ : M ⟶ N)
    (h : (Space.modulePullback B integerBase (hZ B)
        ((arrowSpace B).map ((fibreArrowFunctor ξ).map (prodPointFst a (atlasPoint T))))).map φ =
      (Space.modulePullback B integerBase (hZ B)
        ((arrowSpace B).map ((fibreArrowFunctor ξ).map (prodPointFst a (atlasPoint T))))).map ψ) :
    φ = ψ :=
  Space.QuasiCoherentDescent.modulePullback_map_injective_of_isEtaleCovering B integerBase (hZ B)
    (fun _ : Unit => (arrowSpace B).obj ((fibreArrowFunctor ξ).obj (prodPoint a (atlasPoint T))))
    (fun _ => (arrowSpace B).map ((fibreArrowFunctor ξ).map (prodPointFst a (atlasPoint T))))
    (isEtaleCovering_fst_of_isPullback (isPullback_fibreMap_prodPoint ξ a (atlasPoint T))
      (isAlgebraicSpace_yoneda B integerBase (hZ B) _)
      (isEtaleCovering_fibreFst_atlasPoint ξ)) φ ψ (fun _ => h)

section Full

variable {ξ ξ' : PolarizedSpacesOver B T} (η : baseChangeRepresented ξ ⟶ baseChangeRepresented ξ')

/-- The polarized families of `RepresentedPolarized`, as objects of the Grothendieck construction
of modules on the arrows of the site. -/
abbrev representedPolarizedInclusion :
    RepresentedPolarized B ⥤ Pseudofunctor.CoGrothendieck (arrowModules B) :=
  wideSubcategoryInclusion (cartesianIso B) ⋙ ObjectProperty.ι (IsRepresentedPolarized B)

variable (ξ) in
/-- The base changes of a polarized family, read in the Grothendieck construction, are the
inverse images of `CategoryTheory.Pseudofunctor.CoGrothendieck.inverseImage`. The equality is
proved object by object and morphism by morphism: the two functors agree only after unfolding,
and comparing them as functors would unfold the composition of the Grothendieck construction. -/
theorem baseChangeRepresented_comp_inclusion :
    (baseChangeRepresented ξ).toFunctor ⋙ representedPolarizedInclusion (B := B) =
      Comma.liftConst (R := forget (Space.modulesPseudofunctor B integerBase (hZ B)))
        (fibreArrowFunctor ξ) ((familyPair B T).obj ξ) (fibreSpaceMap ξ)
        (fibreSpaceMap_naturality ξ) ⋙
      inverseImage (Space.modulesPseudofunctor B integerBase (hZ B)) (arrowSpace B) :=
  Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

/-- **`η` as a natural transformation of the families of inverse images.** -/
def fullTheta :=
  NatTrans.transportOfEq (baseChangeRepresented_comp_inclusion ξ)
    (baseChangeRepresented_comp_inclusion ξ')
    (Functor.whiskerRight η.toNatTrans (representedPolarizedInclusion (B := B)))

/-- The components of `fullTheta η` are those of `η`. -/
theorem fullTheta_app (a : (Points T).obj) : (fullTheta η).app a = (η.app a).hom.hom :=
  eq_of_heq (NatTrans.transportOfEq_app_heq _ _ _ a)

/-- The morphism of algebraic spaces `X ⟶ X'` underlying `η` (Stacks 0E93). -/
abbrev fullMap : ((familyPair B T).obj ξ).base ⟶ ((familyPair B T).obj ξ').base :=
  (familyFunctor B T).map (fullBaseMap η)

/-- Each component of `fullTheta η` lies over `fullMap η`: the square formed with the maps
`fibreSpaceMap` to `X` and `X'` commutes. -/
theorem fullTheta_square (a : (Points T).obj) :
    (arrowSpace B).map ((fullTheta η).app a).base ≫ fibreSpaceMap ξ' a =
      fibreSpaceMap ξ a ≫ fullMap η := by
  rw [fullTheta_app]
  exact ObjectProperty.hom_ext _ (yoneda_map_comp_fibreFst_fullBaseMap η a)

/-- The base of each component of `η` is the identity of the point. -/
theorem fullTheta_app_base_right (a : (Points T).obj) :
    (η.app a).hom.hom.base.right = 𝟙 a.base := by
  have : (representedPolarizedProjection B).IsHomLift (𝟙 a.base) (η.app a) := η.isHomLift' a
  have h := IsHomLift.fac' (representedPolarizedProjection B) (𝟙 a.base) (η.app a)
  change (η.app a).hom.hom.base.right = _ at h
  rw [h]
  exact SpacesOverSpace.eqToHom_comp_id_comp_eqToHom _ _

end Full

section Pair

variable (ξ : PolarizedSpacesOver B T)

/-- The fibre product `Z₀ ×_X Z₀` of the base change of the atlas with itself. -/
abbrev atlasPair : AlgebraicSpaces B integerBase (hZ B) :=
  Space.QuasiCoherentDescent.pair B integerBase (hZ B) (X := ((familyPair B T).obj ξ).base)
    (fun _ : Unit => (arrowSpace B).obj ((fibreArrowFunctor ξ).obj (atlasPoint T)))
    (fun _ => fibreSpaceMap ξ (atlasPoint T)) () ()

/-- The first projection of `Z₀ ×_X Z₀`. -/
abbrev atlasPairFst :
    atlasPair ξ ⟶ (arrowSpace B).obj ((fibreArrowFunctor ξ).obj (atlasPoint T)) :=
  Space.QuasiCoherentDescent.pairFst B integerBase (hZ B) (X := ((familyPair B T).obj ξ).base)
    (fun _ : Unit => (arrowSpace B).obj ((fibreArrowFunctor ξ).obj (atlasPoint T)))
    (fun _ => fibreSpaceMap ξ (atlasPoint T)) () ()

/-- The second projection of `Z₀ ×_X Z₀`. -/
abbrev atlasPairSnd :
    atlasPair ξ ⟶ (arrowSpace B).obj ((fibreArrowFunctor ξ).obj (atlasPoint T)) :=
  Space.QuasiCoherentDescent.pairSnd B integerBase (hZ B) (X := ((familyPair B T).obj ξ).base)
    (fun _ : Unit => (arrowSpace B).obj ((fibreArrowFunctor ξ).obj (atlasPoint T)))
    (fun _ => fibreSpaceMap ξ (atlasPoint T)) () ()

/-- The two projections of `Z₀ ×_X Z₀` agree after composing with `Z₀ ⟶ X`. -/
theorem atlasPair_condition :
    atlasPairFst ξ ≫ (fibreSpaceMap ξ (atlasPoint T) : _ ⟶ ((familyPair B T).obj ξ).base) =
      atlasPairSnd ξ ≫ fibreSpaceMap ξ (atlasPoint T) :=
  Space.QuasiCoherentDescent.pair_condition B integerBase (hZ B) _ _ () ()

/-- The base change along the product point `U₀ ×_T U₀`, mapped to `Z₀ ×_X Z₀`. -/
def prodPointPairMap :
    (arrowSpace B).obj ((fibreArrowFunctor ξ).obj (prodPoint (atlasPoint T) (atlasPoint T))) ⟶
      atlasPair ξ :=
  ObjectProperty.homMk (pullback.lift (yoneda.map (fibreMap ξ (prodPointFst _ _)))
    (yoneda.map (fibreMap ξ (prodPointSnd _ _)))
    (isPullback_fibreMap_prodPoint ξ (atlasPoint T) (atlasPoint T)).w)

/-- `prodPointPairMap ξ` followed by the first projection is the base change of the first
projection `U₀ ×_T U₀ ⟶ U₀`. -/
theorem prodPointPairMap_fst :
    prodPointPairMap ξ ≫ atlasPairFst ξ =
      (arrowSpace B).map ((fibreArrowFunctor ξ).map (prodPointFst (atlasPoint T) (atlasPoint T))) :=
  ObjectProperty.hom_ext _ (pullback.lift_fst _ _ _)

/-- `prodPointPairMap ξ` followed by the second projection is the base change of the second
projection `U₀ ×_T U₀ ⟶ U₀`. -/
theorem prodPointPairMap_snd :
    prodPointPairMap ξ ≫ atlasPairSnd ξ =
      (arrowSpace B).map ((fibreArrowFunctor ξ).map (prodPointSnd (atlasPoint T) (atlasPoint T))) :=
  ObjectProperty.hom_ext _ (pullback.lift_snd _ _ _)

/-- The base change along `U₀ ×_T U₀` is `Z₀ ×_X Z₀`. -/
instance isIso_prodPointPairMap_hom : IsIso (prodPointPairMap ξ).hom := by
  have e : (prodPointPairMap ξ).hom =
      (isPullback_fibreMap_prodPoint ξ (atlasPoint T) (atlasPoint T)).isoPullback.hom :=
    pullback.hom_ext ((pullback.lift_fst _ _ _).trans (IsPullback.isoPullback_hom_fst _).symm)
      ((pullback.lift_snd _ _ _).trans (IsPullback.isoPullback_hom_snd _).symm)
  rw [e]
  exact Iso.isIso_hom _

/-- Inverse images along `prodPointPairMap` are injective on morphisms. -/
theorem prodPointPairMap_injective
    {M N : Space.Modules B integerBase (hZ B) (atlasPair ξ).1 (atlasPair ξ).2} (φ ψ : M ⟶ N)
    (h : (Space.modulePullback B integerBase (hZ B) (prodPointPairMap ξ)).map φ =
      (Space.modulePullback B integerBase (hZ B) (prodPointPairMap ξ)).map ψ) : φ = ψ :=
  Space.QuasiCoherentDescent.modulePullback_map_injective_of_isEtaleCovering B integerBase (hZ B)
    (fun _ : Unit => _) (fun _ => prodPointPairMap ξ)
    (Space.isEtaleCovering_of_isIso B integerBase (hZ B) (prodPointPairMap ξ).hom
      (atlasPair ξ).property) φ ψ (fun _ => h)

end Pair


end AlgebraicGeometry.PolarizedOverSpace

end
