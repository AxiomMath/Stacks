module

public import StacksFrontier.AlgebraicGeometry.Quot.ZarConeRelHomSheaf
public import StacksFrontier.AlgebraicGeometry.Quot.RelHomOpensDerivedGluing
public import StacksFrontier.AlgebraicGeometry.Quot.RelHomFunctorNatural
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeDerivedHomDualHeldInputs
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution

/-!
# Zariski gluing of `T ↦ Hom(K_T, E_T)`

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `K`, `E` objects of `D(𝒪_X)` with
`Ext^{-1}(K_V, E_V) = 0` for every algebraic space `V` over `Y`.  For a test scheme `T` over `Y`
and a morphism `h₀ : Z₀ ⟶ T` of the site, the functor `W ↦ Hom(K_{T_W}, E_{T_W})` on the opens of
`Z₀` is identified with the relative Hom functor of the derived pullback along the cone
`AlgebraicGeometry.Space.zarCone` of the base changes `X_{T_W} ⟶ X_{T_{Z₀}}`, at the objects
`Qh(A) ≅ K_{T_{Z₀}}` and `Qh(I) ≅ E_{T_{Z₀}}`, where `I` is a K-injective complex with injective
terms (`AlgebraicGeometry.Space.zarRelHomIso`): this is reindexing, isomorphic diagrams,
postcomposition and conjugation by isomorphisms of objects.  The derived gluing
`CategoryTheory.PullbackData.existsUnique_relHomMap_glue` then applies, its étale inputs being
`AlgebraicGeometry.Space.zarCone_relHomOpens_isFlasque`,
`AlgebraicGeometry.Space.zarCone_isKInjective` and `AlgebraicGeometry.Space.zarCone_isIso_α`.
The remaining input is the sheaf property of the relative Hom presheaves of modules along the
cone (`AlgebraicGeometry.Space.ZarConeRelHomIsSheaf`), proved as
`AlgebraicGeometry.Space.zarConeRelHomIsSheaf`.

The result is `AlgebraicGeometry.Space.RelativeDerivedHomZariskiGluing`, first from that input
(`AlgebraicGeometry.Space.relativeDerivedHomZariskiGluing_of_zarConeRelHomIsSheaf`) and then
outright (`AlgebraicGeometry.Space.relativeDerivedHomZariskiGluing`), and Stacks 0DLC, part (3),
in the case `W = Y`, from Stacks 0DKY alone
(`AlgebraicGeometry.Space.relativeDerivedHomRepresentableOfFibres_of_dual`) or from Stacks 0DKX
alone (`AlgebraicGeometry.Space.relativeDerivedHomRepresentableOfFibres_of_pushforwardBaseChange`).

Nothing here is registered.

## Implementation notes

The section of the gluing pins `HasDerivedCategory.standard` as a local instance: the derived
datum `AlgebraicGeometry.Space.derivedModulePullbackLeftDerived` is built on it, and without the
pin the instance found for the derived category of the modules is a different one.

## References

* [Stacks Project, Tag 0DLC](https://stacks.math.columbia.edu/tag/0DLC)
* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe w u

namespace CategoryTheory

/-- **Gluing along a cover of an open transports along an isomorphism of presheaves of sets.** -/
theorem existsUnique_opensGlue_of_iso {X₀ : Type*} [TopologicalSpace X₀]
    {F G : (Opens X₀)ᵒᵖ ⥤ Type w} (e : F ≅ G) {U : Opens X₀} {ι : Type*} (V : ι → Opens X₀)
    (hV : ∀ i, V i ≤ U)
    (hG : ∀ x : ∀ i, G.obj (Opposite.op (V i)),
      (∀ i k, G.map (homOfLE (inf_le_left : V i ⊓ V k ≤ V i)).op (x i) =
        G.map (homOfLE (inf_le_right : V i ⊓ V k ≤ V k)).op (x k)) →
      ∃! y : G.obj (Opposite.op U), ∀ i, G.map (homOfLE (hV i)).op y = x i)
    (x : ∀ i, F.obj (Opposite.op (V i)))
    (hx : ∀ i k, F.map (homOfLE (inf_le_left : V i ⊓ V k ≤ V i)).op (x i) =
      F.map (homOfLE (inf_le_right : V i ⊓ V k ≤ V k)).op (x k)) :
    ∃! y : F.obj (Opposite.op U), ∀ i, F.map (homOfLE (hV i)).op y = x i := by
  obtain ⟨y, hy, hyu⟩ := hG (fun i => e.hom.app _ (x i)) fun i k => by
    rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, hx]
  refine ⟨e.inv.app _ y, fun i => ?_, fun y' hy' => ?_⟩
  · rw [← NatTrans.naturality_apply, hy, Iso.hom_inv_id_app_apply]
  · rw [← hyu (e.hom.app _ y') fun i => by rw [← NatTrans.naturality_apply, hy'],
      Iso.hom_inv_id_app_apply]

namespace PullbackData

/-- **`CategoryTheory.PullbackData.existsUnique_relHomMap_glue` for the relative Hom functor**:
the same gluing, with the morphisms over the opens read as the values of
`CategoryTheory.PullbackData.relHomFunctor` of the derived datum. -/
theorem existsUnique_relHomFunctor_glue {X₀ : Type*} [TopologicalSpace X₀] {A : Type*}
    [Category* A] {M : A → Type*} [∀ a, Category* (M a)] [∀ a, Abelian (M a)]
    [∀ a, HasDerivedCategory.{w} (M a)] (P : PullbackData A M)
    [∀ {a b : A} (f : a ⟶ b), (P.pull f).Additive] (hP : P.IsCoherent)
    (E : P.mapHomotopyCategory.LeftDerived (fun a => DerivedCategory (M a)))
    (hE : E.toPullbackData.IsCoherent) {π : Opens X₀ ⥤ A} {a₀ : A} (κ : ConeTo π a₀)
    (K L : CochainComplex (M a₀) ℤ) (hQ : ∀ a, E.Q a = DerivedCategory.Qh)
    (hsh : ∀ N N' : M a₀, (P.relHomOpens hP κ N N').IsSheaf)
    (hfl : ∀ N N' : M a₀, Injective N' → (P.relHomOpens hP κ N N').IsFlasque)
    (hL : ∀ p, Injective (L.X p)) (hKi : ∀ W, (P.legComplex κ L W).IsKInjective)
    (hα : ∀ W N, IsIso ((E.α (κ.leg W)).app N))
    (hneg : ∀ W, Subsingleton ((E.L (κ.leg W)).obj
        ((E.Q a₀).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) ⟶
      ((E.L (κ.leg W)).obj
        ((E.Q a₀).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L)))⟦(-1 : ℤ)⟧))
    {U : Opens X₀} {ι : Type*} (V : ι → Opens X₀) (hV : ∀ i, V i ≤ U) (hsup : iSup V = U)
    (x : ∀ i, (E.toPullbackData.relHomFunctor hE κ
      ((E.Q a₀).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
      ((E.Q a₀).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L))).obj
        (Opposite.op (V i)))
    (hx : ∀ i k, (E.toPullbackData.relHomFunctor hE κ _ _).map
        (homOfLE (inf_le_left : V i ⊓ V k ≤ V i)).op (x i) =
      (E.toPullbackData.relHomFunctor hE κ _ _).map
        (homOfLE (inf_le_right : V i ⊓ V k ≤ V k)).op (x k)) :
    ∃! y : (E.toPullbackData.relHomFunctor hE κ
        ((E.Q a₀).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
        ((E.Q a₀).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L))).obj
          (Opposite.op U),
      ∀ i, (E.toPullbackData.relHomFunctor hE κ _ _).map (homOfLE (hV i)).op y = x i :=
  P.existsUnique_relHomMap_glue hP E κ K L hQ hsh hfl hL hKi hα hneg V hV hsup x hx

variable {A : Type*} [Category* A] {D : A → Type*} [∀ a, Category* (D a)] (P : PullbackData A D)
  (hP : P.IsCoherent) {I : Type*} [Category* I] {π : I ⥤ A} {a₀ : A} (κ : ConeTo π a₀)

/-- **Isomorphic objects have isomorphic relative Hom functors**: for `a : M' ≅ M` and
`b : N ≅ N'`, composition with the inverse images of `a` and `b`. -/
def relHomFunctorCongr {M N M' N' : D a₀} (a : M' ≅ M) (b : N ≅ N') :
    P.relHomFunctor hP κ M N ≅ P.relHomFunctor hP κ M' N' :=
  NatIso.ofComponents
    (fun i => Equiv.toIso (Iso.homCongr ((P.pull (κ.leg i.unop)).mapIso a).symm
      ((P.pull (κ.leg i.unop)).mapIso b)))
    (fun {i j} g => by
      ext β
      exact P.isTriangleNatural_comp a.hom b.hom (π.map g.unop) (κ.leg i.unop) (κ.leg j.unop)
        (κ.w g.unop) β)

end PullbackData

end CategoryTheory

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The top open -/

section Top

variable {Y : AlgebraicSpaces B S hS} (T : SchemesOver Y) {Z₀ : BigFppfOver B S hS}
  (h₀ : Z₀ ⟶ T.left)

/-- The inverse of the inclusion of the top open of `Z₀`. -/
def zarTopLift : Z₀ ⟶ BigFppfOver.openSubObj B S hS Z₀ ⊤ :=
  openSubObjLift B S hS Z₀ ⊤ (𝟙 Z₀) fun _ _ => trivial

/-- `zarTopLift` followed by the inclusion of the top open of `Z₀` is the identity of `Z₀`. -/
theorem zarTopLift_comp_openSubHom :
    zarTopLift (B := B) (S := S) (hS := hS) (Z₀ := Z₀) ≫ BigFppfOver.openSubHom B S hS Z₀ ⊤ =
      𝟙 Z₀ :=
  openSubObjLift_comp_openSubHom B S hS _ _ _ _

/-- The inclusion of the top open of `Z₀` followed by `zarTopLift` is the identity of the top
open. -/
theorem openSubHom_comp_zarTopLift :
    BigFppfOver.openSubHom B S hS Z₀ ⊤ ≫ zarTopLift (B := B) (S := S) (hS := hS) (Z₀ := Z₀) =
      𝟙 _ := by
  have := mono_openSubHom B S hS Z₀ ⊤
  rw [← cancel_mono (BigFppfOver.openSubHom B S hS Z₀ ⊤), Category.assoc,
    zarTopLift_comp_openSubHom, Category.comp_id, Category.id_comp]

/-- **The test scheme over the top open of `Z₀` is the restriction of `T` to `Z₀`.** -/
def zarTopIso : (zarOpensTest T h₀).obj ⊤ ≅ restrictTest T h₀ where
  hom := zarLeg T h₀ ⊤
  inv := restrictTestMap T zarTopLift (by
    rw [← Category.assoc, zarTopLift_comp_openSubHom, Category.id_comp])
  hom_inv_id := CostructuredArrow.hom_ext _ _ openSubHom_comp_zarTopLift
  inv_hom_id := CostructuredArrow.hom_ext _ _ zarTopLift_comp_openSubHom

end Top

/-! ### The relative Hom functor over the opens -/

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (T : SchemesOver Y)
  {Z₀ : BigFppfOver B S hS} (h₀ : Z₀ ⟶ T.left)

/-- The legs of the cone of base changes over the opens, followed by the projection to `X`, are
the projections to `X`. -/
theorem zarCone_leg_comp_projection (W : Z₀.left.obj.Opens) :
    (zarCone f T h₀).leg W ≫ baseChangeProjection f (restrictTest T h₀) =
      overProjection f ((schemesOverToOver Y).obj ((zarOpensTest T h₀).obj W)) :=
  overBaseChangeMap_comp_projection f _

/-- **`W ↦ Hom(K_{T_W}, E_{T_W})` as the relative Hom functor along the cone of base changes**:
for isomorphisms `a : M ≅ K_{T_{Z₀}}` and `b : E_{T_{Z₀}} ≅ N`, the functor
`W ↦ Hom(K_{T_W}, E_{T_W})` on the opens of `Z₀` is the relative Hom functor of `M`, `N` along
`AlgebraicGeometry.Space.zarCone`.  This is reindexing, isomorphic diagrams, postcomposition with
the projection `X_{T_{Z₀}} ⟶ X` and conjugation by `a` and `b`. -/
def zarRelHomIso (K E : derivedModules B S hS X)
    {M N : derivedModules B S hS (baseChangeSpace f (restrictTest T h₀))}
    (a : M ≅ ((smallEtaleDerivedPullbackData B S hS).pull
      (baseChangeProjection f (restrictTest T h₀))).obj K)
    (b : ((smallEtaleDerivedPullbackData B S hS).pull
      (baseChangeProjection f (restrictTest T h₀))).obj E ≅ N) :
    (zarOpensTest T h₀).op ⋙ relativeDerivedHom f K E ≅
      (smallEtaleDerivedPullbackData B S hS).relHomFunctor
        (smallEtaleDerivedPullbackData_isCoherent B S hS) (zarCone f T h₀) M N :=
  (smallEtaleDerivedPullbackData B S hS).relHomFunctorReindexIso
      (smallEtaleDerivedPullbackData_isCoherent B S hS)
      (zarOpensTest T h₀ ⋙ schemesOverToOver Y) (overBaseChangeCone f) K E ≪≫
    ((smallEtaleDerivedPullbackData B S hS).relHomIsoOfIso
      (smallEtaleDerivedPullbackData_isCoherent B S hS)
      ((overBaseChangeCone f).reindex (zarOpensTest T h₀ ⋙ schemesOverToOver Y))
      ((zarCone f T h₀).postcomp (baseChangeProjection f (restrictTest T h₀)))
      (Iso.refl _) (fun W => (Category.id_comp _).trans (zarCone_leg_comp_projection f T h₀ W))
      K E).symm ≪≫
    ((smallEtaleDerivedPullbackData B S hS).relHomPostcompIso
      (smallEtaleDerivedPullbackData_isCoherent B S hS) (zarCone f T h₀)
      (baseChangeProjection f (restrictTest T h₀)) K E).symm ≪≫
    (smallEtaleDerivedPullbackData B S hS).relHomFunctorCongr
      (smallEtaleDerivedPullbackData_isCoherent B S hS) (zarCone f T h₀) a b

/-- **The vanishing of `Ext⁻¹` along the legs**, transported from the base changes `X_{T_W}` to the
inverse images of `M ≅ K_{T_{Z₀}}` and `N ≅ E_{T_{Z₀}}` along the legs of the cone. -/
theorem zarCone_subsingleton_pull_shift (K E : derivedModules B S hS X)
    (hneg : ∀ V : Over Y,
      Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj K ⟶
        (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj E)⟦(-1 : ℤ)⟧))
    {M N : derivedModules B S hS (baseChangeSpace f (restrictTest T h₀))}
    (a : M ≅ ((smallEtaleDerivedPullbackData B S hS).pull
      (baseChangeProjection f (restrictTest T h₀))).obj K)
    (b : ((smallEtaleDerivedPullbackData B S hS).pull
      (baseChangeProjection f (restrictTest T h₀))).obj E ≅ N) (W : Z₀.left.obj.Opens) :
    Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull ((zarCone f T h₀).leg W)).obj M ⟶
      (((smallEtaleDerivedPullbackData B S hS).pull ((zarCone f T h₀).leg W)).obj N)⟦(-1 : ℤ)⟧) :=
  (subsingleton_hom_shift_congr
    (((smallEtaleDerivedPullbackData B S hS).triangle
      (zarCone_leg_comp_projection f T h₀ W)).app K ≪≫
        ((smallEtaleDerivedPullbackData B S hS).pull ((zarCone f T h₀).leg W)).mapIso a.symm)
    (((smallEtaleDerivedPullbackData B S hS).triangle
      (zarCone_leg_comp_projection f T h₀ W)).app E ≪≫
        ((smallEtaleDerivedPullbackData B S hS).pull ((zarCone f T h₀).leg W)).mapIso b)
    (-1)).1 (hneg _)

/-! ### The gluing -/

section Glue

attribute [local instance] HasDerivedCategory.standard

/-- **Gluing of `W ↦ Hom(K_{T_W}, E_{T_W})` over the opens of `Z₀`**: if the relative Hom
presheaves of modules along the cone of base changes are sheaves (`hsh`) and `Ext⁻¹(K_V, E_V) = 0`
for every algebraic space `V` over `Y` (`hneg`), morphisms over the members of an open covering of
`Z₀` which agree on the overlaps come from exactly one morphism over the top open.  This is
`CategoryTheory.PullbackData.existsUnique_relHomMap_glue` at `AlgebraicGeometry.Space.zarCone`,
read through `AlgebraicGeometry.Space.zarRelHomIso` with `I` a K-injective resolution with
injective terms. -/
theorem existsUnique_zarOpens_glue (K E : derivedModules B S hS X)
    (hsh : ZarConeRelHomIsSheaf f T h₀)
    (hneg : ∀ V : Over Y,
      Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj K ⟶
        (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj E)⟦(-1 : ℤ)⟧))
    {ι : Type*} (U : ι → Z₀.left.obj.Opens) (hU : iSup U = ⊤)
    (x : ∀ i, ((zarOpensTest T h₀).op ⋙ relativeDerivedHom f K E).obj (Opposite.op (U i)))
    (hx : ∀ i k, ((zarOpensTest T h₀).op ⋙ relativeDerivedHom f K E).map
        (homOfLE (inf_le_left : U i ⊓ U k ≤ U i)).op (x i) =
      ((zarOpensTest T h₀).op ⋙ relativeDerivedHom f K E).map
        (homOfLE (inf_le_right : U i ⊓ U k ≤ U k)).op (x k)) :
    ∃! y : ((zarOpensTest T h₀).op ⋙ relativeDerivedHom f K E).obj (Opposite.op ⊤),
      ∀ i, ((zarOpensTest T h₀).op ⋙ relativeDerivedHom f K E).map
        (homOfLE (le_top : U i ≤ ⊤)).op y = x i := by
  let C := Modules.{u, u} B S hS (baseChangeSpace f (restrictTest T h₀)).1
    (baseChangeSpace f (restrictTest T h₀)).2
  have : IsGrothendieckAbelian.{u} C := by
    have : EssentiallySmall.{u} (smallEtaleRingedSite B S hS
        (baseChangeSpace f (restrictTest T h₀)).1 (baseChangeSpace f (restrictTest T h₀)).2).C := by
      show EssentiallySmall.{u} (SmallEtale B S hS (baseChangeSpace f (restrictTest T h₀)).1)
      infer_instance
    exact SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _
  let r := baseChangeProjection f (restrictTest T h₀)
  let K' := ((smallEtaleDerivedPullbackData B S hS).pull r).obj K
  let E' := ((smallEtaleDerivedPullbackData B S hS).pull r).obj E
  let A := (DerivedCategory.Q (C := C)).objPreimage K'
  let E₀ := (DerivedCategory.Q (C := C)).objPreimage E'
  let J := (Stacks.Injectives.kInjectiveResolutionFunctor.{u} C).obj E₀
  let j := (Stacks.Injectives.kInjectiveResolutionInclusion.{u} C).app E₀
  let a : DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj A) ≅ K' :=
    (DerivedCategory.quotientCompQhIso C).app A ≪≫ DerivedCategory.Q.objObjPreimageIso K'
  let b : E' ≅ DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj J) :=
    (DerivedCategory.Q.objObjPreimageIso E').symm ≪≫ asIso (DerivedCategory.Q.map j) ≪≫
      ((DerivedCategory.quotientCompQhIso C).app J).symm
  exact existsUnique_opensGlue_of_iso (zarRelHomIso f T h₀ K E a b) U (fun _ => le_top)
    (fun z hz => CategoryTheory.PullbackData.existsUnique_relHomFunctor_glue
      (modulePullbackDataTopos B S hS) (modulePullbackDataTopos_isCoherent B S hS)
      (derivedModulePullbackLeftDerived B S hS) (smallEtaleDerivedPullbackData_isCoherent B S hS)
      (zarCone f T h₀) A J (fun _ => rfl) hsh
      (fun N N' _ => zarCone_relHomOpens_isFlasque f T h₀ N N') (fun _ => inferInstance)
      (zarCone_isKInjective f T h₀ J inferInstance) (zarCone_isIso_α f T h₀)
      (zarCone_subsingleton_pull_shift f T h₀ K E hneg a b) U (fun _ => le_top) hU z hz) x hx

end Glue

/-- **Zariski gluing of `T ↦ Hom(K_T, E_T)` for fixed `K`, `E`**: if the relative Hom presheaves
of modules along the cones of base changes over the opens are sheaves (`hsh`) and
`Ext⁻¹(K_V, E_V) = 0` for every algebraic space `V` over `Y` (`hneg`), then
`T ↦ Hom(K_T, E_T)` is a Zariski sheaf.  The gluing over the top open of `Z₀`
(`AlgebraicGeometry.Space.existsUnique_zarOpens_glue`) is moved to the restriction of `T` to `Z₀`
along `AlgebraicGeometry.Space.zarTopIso`. -/
theorem isZariskiSheafOver_relativeDerivedHom (K E : derivedModules B S hS X)
    (hsh : ∀ (T : SchemesOver Y) {Z₀ : BigFppfOver B S hS} (h₀ : Z₀ ⟶ T.left),
      ZarConeRelHomIsSheaf f T h₀)
    (hneg : ∀ V : Over Y,
      Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj K ⟶
        (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj E)⟦(-1 : ℤ)⟧)) :
    IsZariskiSheafOver (relativeDerivedHom f K E) := by
  intro T Z₀ h₀ ι U hU α hα
  let R := relativeDerivedHom f K E
  let σ := zarTopIso T h₀
  obtain ⟨y, hy, hyu⟩ := existsUnique_zarOpens_glue f T h₀ K E (hsh T h₀) hneg U hU α hα
  have key : ∀ (g : R.obj (Opposite.op (restrictTest T h₀))) (i : ι),
      R.map (zarLeg T h₀ (U i)).op g =
        ((zarOpensTest T h₀).op ⋙ R).map (homOfLE (le_top : U i ≤ ⊤)).op (R.map σ.hom.op g) := by
    intro g i
    show _ = R.map ((zarOpensTest T h₀).map (homOfLE (le_top : U i ≤ ⊤))).op
      (R.map (zarLeg T h₀ ⊤).op g)
    rw [← Functor.map_comp_apply, ← op_comp, zarLeg_w]
  refine ⟨R.map σ.inv.op y, fun i => ?_, fun g hg => ?_⟩
  · refine (key _ i).trans ?_
    rw [← Functor.map_comp_apply R σ.inv.op σ.hom.op, ← op_comp, Iso.hom_inv_id, op_id,
      Functor.map_id_apply]
    exact hy i
  · have hgy : R.map σ.hom.op g = y := hyu _ fun i => (key g i).symm.trans (hg i)
    rw [← hgy, ← Functor.map_comp_apply R σ.hom.op σ.inv.op, ← op_comp, Iso.inv_hom_id,
      op_id, Functor.map_id_apply]

/-- **`AlgebraicGeometry.Space.RelativeDerivedHomZariskiGluing` from the sheaf property of the
relative Hom presheaves of modules** along every cone of base changes over the opens
(`AlgebraicGeometry.Space.ZarConeRelHomIsSheaf`, `hsh`, internal, in progress). -/
theorem relativeDerivedHomZariskiGluing_of_zarConeRelHomIsSheaf
    (hsh : ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (T : SchemesOver Y)
      {Z₀ : BigFppfOver B S hS} (h₀ : Z₀ ⟶ T.left), ZarConeRelHomIsSheaf f T h₀) :
    RelativeDerivedHomZariskiGluing B S hS :=
  fun f K E _ _ hneg => isZariskiSheafOver_relativeDerivedHom f K E
    (fun T _ h₀ => hsh f T h₀) (fun V => hneg V (-1) (by decide))

/-- **Stacks 0DLC, part (3), in the case `W = Y`, from Stacks 0DKY and the sheaf property of the
relative Hom presheaves of modules**:
`AlgebraicGeometry.Space.relativeDerivedHomRepresentableOfFibres_of_dual_of_zariskiGluing` with
Zariski gluing discharged by
`AlgebraicGeometry.Space.relativeDerivedHomZariskiGluing_of_zarConeRelHomIsSheaf`.  The inputs are
Stacks 0DKY in its compatible form (`h0DKY`) and `hsh` (internal, in progress). -/
theorem relativeDerivedHomRepresentableOfFibres_of_dual_of_zarConeRelHomIsSheaf
    (h0DKY : RelativeDerivedHomDualExistsNaturalCompatible B S hS)
    (hsh : ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (T : SchemesOver Y)
      {Z₀ : BigFppfOver B S hS} (h₀ : Z₀ ⟶ T.left), ZarConeRelHomIsSheaf f T h₀) :
    RelativeDerivedHomRepresentableOfFibres B S hS :=
  relativeDerivedHomRepresentableOfFibres_of_dual_of_zariskiGluing h0DKY
    (relativeDerivedHomZariskiGluing_of_zarConeRelHomIsSheaf hsh)

/-- **Stacks 0DLC, part (3), in the case `W = Y`, from Stacks 0DKX and the sheaf property of the
relative Hom presheaves of modules**: Stacks 0DKY is discharged by
`relativeDerivedHomDualExistsNaturalCompatible_of_relativelyPerfectPushforwardBaseChange`.
The inputs are Stacks 0DKX (`h0DKX`, not yet proved here) and `hsh` (internal, in
progress). -/
theorem relativeDerivedHomRepresentableOfFibres_of_pushforwardBaseChange_of_zarConeRelHomIsSheaf
    (h0DKX : RelativelyPerfectPushforwardBaseChange B S hS)
    (hsh : ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (T : SchemesOver Y)
      {Z₀ : BigFppfOver B S hS} (h₀ : Z₀ ⟶ T.left), ZarConeRelHomIsSheaf f T h₀) :
    RelativeDerivedHomRepresentableOfFibres B S hS :=
  relativeDerivedHomRepresentableOfFibres_of_dual_of_zarConeRelHomIsSheaf
    (relativeDerivedHomDualExistsNaturalCompatible_of_relativelyPerfectPushforwardBaseChange
      B S hS h0DKX) hsh

/-! ### The sheaf property discharged -/

variable (B S hS) in
/-- **Zariski gluing of `T ↦ Hom(K_T, E_T)`**:
`AlgebraicGeometry.Space.RelativeDerivedHomZariskiGluing`, with the sheaf property of the
relative Hom presheaves of modules discharged by
`AlgebraicGeometry.Space.zarConeRelHomIsSheaf`. -/
theorem relativeDerivedHomZariskiGluing : RelativeDerivedHomZariskiGluing B S hS :=
  relativeDerivedHomZariskiGluing_of_zarConeRelHomIsSheaf fun f T _ h₀ =>
    zarConeRelHomIsSheaf f T h₀

/-- **Stacks 0DLC, part (3), in the case `W = Y`, from Stacks 0DKY**: the only input is Stacks
0DKY in its compatible form (`h0DKY`, pending). -/
theorem relativeDerivedHomRepresentableOfFibres_of_dual
    (h0DKY : RelativeDerivedHomDualExistsNaturalCompatible B S hS) :
    RelativeDerivedHomRepresentableOfFibres B S hS :=
  relativeDerivedHomRepresentableOfFibres_of_dual_of_zariskiGluing h0DKY
    (relativeDerivedHomZariskiGluing B S hS)

/-- **Stacks 0DLC, part (3), in the case `W = Y`, from Stacks 0DKX**: the only input is Stacks
0DKX (`h0DKX`, not yet proved here). -/
theorem relativeDerivedHomRepresentableOfFibres_of_pushforwardBaseChange
    (h0DKX : RelativelyPerfectPushforwardBaseChange B S hS) :
    RelativeDerivedHomRepresentableOfFibres B S hS :=
  relativeDerivedHomRepresentableOfFibres_of_dual
    (relativeDerivedHomDualExistsNaturalCompatible_of_relativelyPerfectPushforwardBaseChange
      B S hS h0DKX)

end AlgebraicGeometry.Space

end
