module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkPullbackGerm
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingForget
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantCoefficients
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartLocalRingSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingFieldSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRingedToposHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkStructureMap
public import StacksFrontier.CategoryTheory.Sites.Point.OpensPointModuleFiberStalk
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesComparison
public import
  StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesComparisonPullback

/-!
# Stalks of `ε^*` at the geometric points of a representable algebraic space

Let `X = yoneda.obj U` be the algebraic space represented by an object `U` of the big fppf site
over `S`, with underlying scheme `X_0`, and let `ε : (X_étale, 𝒪_X) ⟶ (X_{0,Zar}, 𝒪_{X_0})` be
`AlgebraicGeometry.Space.representedZariskiRingedToposHomRepresentedZariskiRingedToposHom`. For a
geometric point `x̄` of `X` lying over the point `x` of `X_0`, the stalk of `ε^*M` at `x̄` is
`M_x ⊗_{𝒪_{X_0, x}} 𝒪_{X, x̄}`.

## Main results

* `AlgebraicGeometry.toPresheafFiber_sheafFiberIsoOfAdjOfFiberIso_inv_sheafFiber_map`:
  the comparison of fibre functors along a continuous functor of sites, on germs.
-/

@[expose] public noncomputable section

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

universe z uC vC uD vD uA vA

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  {D : Type uD} [Category.{vD} D] {K : GrothendieckTopology D}
  (p : J.Point.{z}) (q : K.Point.{z}) (G : C ⥤ D) [G.IsContinuous J K]
  (e : G ⋙ q.fiber ≅ p.fiber)
  {A : Type uA} [Category.{vA} A] [HasProducts.{z} A] [HasColimitsOfSize.{z, z} A]
  {L : Sheaf J A ⥤ Sheaf K A} (adj : L ⊣ G.sheafPushforwardContinuous A J K)

/-- **The comparison of fibre functors along a continuous functor of sites, on germs.**  The
germ at `w ∈ p.fiber U` of a section of `F`, carried to the fibre at `q` of `L F` and then
along `φ : L F ⟶ M`, is the germ at the corresponding lift `e⁻¹ w ∈ q.fiber (G U)` of the
transpose of `φ` applied to that section. -/
theorem toPresheafFiber_sheafFiberIsoOfAdjOfFiberIso_inv_sheafFiber_map
    (F : Sheaf J A) (M : Sheaf K A) (φ : L.obj F ⟶ M) (U : C) (w : p.fiber.obj U) :
    p.toPresheafFiber U w F.obj ≫ (sheafFiberIsoOfAdjOfFiberIso p q G e adj).inv.app F ≫
        q.sheafFiber.map φ =
      (adj.homEquiv F M φ).hom.app (op U) ≫ q.toPresheafFiber (G.obj U) (e.inv.app U w) M.obj := by
  let M' := q.sheafFiber.obj M
  let adj₁ := adj.comp q.skyscraperSheafAdjunction
  let ee := Functor.flipping.functor.mapIso
    (Functor.isoWhiskerRight (NatIso.op e.symm) (piFunctor (C := A)).flip)
  let e' : q.skyscraperSheafFunctor ⋙ G.sheafPushforwardContinuous A J K ≅
      p.skyscraperSheafFunctor := NatIso.ofComponents
    (fun N => (fullyFaithfulSheafToPresheaf J A).preimageIso (ee.app N))
    (by intro N N' f; ext U; exact congrArg (fun k => k.app U) (ee.hom.naturality f))
  have hinv : (sheafFiberIsoOfAdjOfFiberIso p q G e adj).inv.app F =
      ((conjugateIsoEquiv adj₁ p.skyscraperSheafAdjunction).symm e').hom.app F := rfl
  have he' : (e'.hom.app M').hom.app (op U) ≫ Pi.π (fun _ : p.fiber.obj U => M') w =
      Pi.π (fun _ : q.fiber.obj (G.obj U) => M') (e.inv.app U w) := by
    show Pi.map' (f := fun _ : q.fiber.obj (G.obj U) => M') (g := fun _ : p.fiber.obj U => M')
      (fun w => e.inv.app U w) (fun _ => 𝟙 M') ≫ Pi.π (fun _ : p.fiber.obj U => M') w = _
    rw [Pi.map'_comp_π, Category.comp_id]
  let c := p.skyscraperSheafAdjunction.homEquiv F M'
    (((conjugateIsoEquiv adj₁ p.skyscraperSheafAdjunction).symm e').hom.app F ≫
      q.sheafFiber.map φ)
  have h1 := GrothendieckTopology.Point.toPresheafFiber_comp_skyscraperSheafAdjunction_homEquiv_symm
    p F M' c U w
  rw [Equiv.symm_apply_apply] at h1
  rw [hinv]
  refine h1.trans ?_
  have h2 : c = adj₁.homEquiv F M' (q.sheafFiber.map φ) ≫ e'.hom.app M' :=
    Adjunction.mate_homEquiv adj₁ p.skyscraperSheafAdjunction e' (q.sheafFiber.map φ)
  have h3 : adj₁.homEquiv F M' (q.sheafFiber.map φ) =
      adj.homEquiv F M φ ≫ (G.sheafPushforwardContinuous A J K).map
        (q.skyscraperSheafAdjunction.homEquiv M M' (𝟙 _)) := by
    have h4 : q.skyscraperSheafAdjunction.homEquiv (L.obj F) M' (q.sheafFiber.map φ) =
        φ ≫ q.skyscraperSheafAdjunction.homEquiv M M' (𝟙 _) := by
      rw [← Adjunction.homEquiv_naturality_left, Category.comp_id]
    rw [Adjunction.comp_homEquiv, Equiv.trans_apply, h4, Adjunction.homEquiv_naturality_right]
  rw [h2, h3]
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  have h5 : (q.skyscraperSheafAdjunction.homEquiv M M' (𝟙 _)).hom.app (op (G.obj U)) ≫
      (e'.hom.app M').hom.app (op U) ≫ Pi.π (fun _ : p.fiber.obj U => M') w =
        q.toPresheafFiber (G.obj U) (e.inv.app U w) M.obj :=
    (congrArg (fun t => (q.skyscraperSheafAdjunction.homEquiv M M' (𝟙 _)).hom.app
      (op (G.obj U)) ≫ t) he').trans
      (GrothendieckTopology.Point.skyscraperSheafAdjunction_unit_π q M (G.obj U) (e.inv.app U w))
  exact ((Category.assoc _ _ _).trans (Category.assoc _ _ _)).trans
    (congrArg (fun t => (adj.homEquiv F M φ).hom.app (op U) ≫ t) h5)

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

open IsLocalRing

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T : BigFppfOver B S hS}
  (x : GeometricPoint B S hS (yoneda.obj T))

/-- The point of the scheme underlying `T` under a geometric point of `yoneda.obj T`. -/
abbrev representedPoint : representedSchemeRepresentedZariskiRingedToposHom B S hS T :=
  chartPoint B S hS (yoneda.obj T) (yonedaIdentityNeighborhood T x)

/-- A lift of `x̄` into the étale chart given by an open `V` composes with the inclusion of the
chart open to give `x̄`. -/
private theorem geometricFiber_comp_chartOpenOverι
    (V : (representedSchemeRepresentedZariskiRingedToposHom B S hS T).Opens)
    (p : GeometricFiber B S hS (yoneda.obj T) x
      ((representedSchemeOpensToSmallEtaleRepresentedZariskiRingedToposHom B S hS T).obj V)) :
    p.1 ≫ chartOpenOverι B S hS ((yonedaIdentityNeighborhood T x).chart) V =
      x.val.value := p.2

/-- A lift of `x̄` into the étale chart given by an open `V` of the scheme underlying `T`
exists only if the point under `x̄` lies in `V`. -/
theorem representedPoint_mem_of_geometricFiber
    (V : (representedSchemeRepresentedZariskiRingedToposHom B S hS T).Opens)
    (p : GeometricFiber B S hS (yoneda.obj T) x
      ((representedSchemeOpensToSmallEtaleRepresentedZariskiRingedToposHom B S hS T).obj V)) :
    representedPoint x ∈ V := by
  have h := geometricFiber_comp_chartOpenOverι x V p
  have hx : representedPoint x = V.ι.base
      (((BigFppfOver.toScheme B S hS).map p.1).base (closedPoint _)) := by
    have h' := congrArg (fun k : x.val.siteObject ⟶ T => ((BigFppfOver.toScheme B S hS).map k).base
      (closedPoint (chartGeometricPoint (yonedaIdentityNeighborhood T x)).residueField)) h
    exact h'.symm.trans <| congrArg (fun k : (BigFppfOver.toScheme B S hS).obj x.val.siteObject ⟶
        representedSchemeRepresentedZariskiRingedToposHom B S hS T => k.base
          (closedPoint (chartGeometricPoint (yonedaIdentityNeighborhood T x)).residueField))
      ((BigFppfOver.toScheme B S hS).map_comp p.1
        (chartOpenOverι B S hS ((yonedaIdentityNeighborhood T x).chart) V))
  rw [hx]
  exact (((BigFppfOver.toScheme B S hS).map p.1).base (closedPoint _)).2

/-- Lifts of `x̄` into the étale chart given by an open of the scheme underlying `T` are
unique. -/
theorem representedGeometricFiber_ext
    (V : (representedSchemeRepresentedZariskiRingedToposHom B S hS T).Opens)
    (p q : GeometricFiber B S hS (yoneda.obj T) x
      ((representedSchemeOpensToSmallEtaleRepresentedZariskiRingedToposHom B S hS T).obj V)) :
    p = q := by
  apply Subtype.ext
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  refine (cancel_mono V.ι).1 ?_
  have hp := geometricFiber_comp_chartOpenOverι x V p
  have hq := geometricFiber_comp_chartOpenOverι x V q
  exact congrArg (fun k => k.left.hom) (hp.trans hq.symm)

/-- The inclusion of the Zariski opens of the scheme underlying `T` into the small étale site
of `yoneda.obj T` is continuous. -/
instance isContinuous_representedSchemeOpensToSmallEtale :
    (representedSchemeOpensToSmallEtaleRepresentedZariskiRingedToposHom B S hS T).IsContinuous
      (Opens.grothendieckTopology ↥(representedSchemeRepresentedZariskiRingedToposHom B S hS T))
      (SmallEtale.topology B S hS (yoneda.obj T)) :=
  have := _root_.AlgebraicGeometry.SmallEtale.isContinuous_opensToSmallEtale
    (associatedBigEtaleSite B) (representedSchemeRepresentedZariskiRingedToposHom B S hS T)
        T.left.property
  Functor.isContinuous_comp _ _ _
    (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
      (representedSchemeRepresentedZariskiRingedToposHom B S hS T) T.left.property) _

/-- The point of the small étale site of `yoneda.obj T` given by `x̄`. -/
abbrev yonedaEtaleSitePoint :
    (SmallEtale.topology B S hS (yoneda.obj T)).Point.{u} :=
  etaleSitePoint B S hS (yoneda.obj T) x (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T)

/-- The lifts of `x̄` into the étale chart given by an open `V` of the scheme underlying `T` are
the proofs that `V` contains the point under `x̄`. -/
def representedFiberIso :
    representedSchemeOpensToSmallEtaleRepresentedZariskiRingedToposHom B S hS T ⋙
        (yonedaEtaleSitePoint x).fiber ≅
      (Opens.pointGrothendieckTopology (representedPoint x)).fiber :=
  NatIso.ofComponents (fun V => Equiv.toIso
    { toFun := fun p => ⟨⟨representedPoint_mem_of_geometricFiber x V p⟩⟩
      invFun := fun h => ⟨chartOpenPoint B S hS (yonedaIdentityNeighborhood T x) V h.down.down,
        (chartOpenNeighborhood B S hS (yonedaIdentityNeighborhood T x) V h.down.down).point_comp⟩
      left_inv := fun p => representedGeometricFiber_ext x V _ _
      right_inv := fun _ => Subsingleton.elim _ _ })
    (fun _ => by ext; exact Subsingleton.elim _ _)

/-- **The matched pair of points of `ε`.**  The stalk at the point `x` of the scheme underlying
`T` of a sheaf of sets is the stalk at `x̄` of its inverse image along `ε`. -/
def representedSheafFiberIso :
    (Opens.pointGrothendieckTopology (representedPoint x)).sheafFiber (A := Type u) ≅
      (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom
        B S hS T).toToposHom.inverseImage ⋙
        (yonedaEtaleSitePoint x).sheafFiber (A := Type u) :=
  (sheafFiberIsoOfAdjOfFiberIso (Opens.pointGrothendieckTopology (representedPoint x))
    (yonedaEtaleSitePoint x)
    (representedSchemeOpensToSmallEtaleRepresentedZariskiRingedToposHom B S hS T)
    (representedFiberIso x)
    (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS T).toToposHom.adj).symm

/-- **The homomorphism `𝒪_{X_0, x} ⟶ 𝒪_{X, x̄}` of stalk rings** along which `ε^*` extends
scalars at `x̄`, for the matched pair of points
`AlgebraicGeometry.Space.representedSheafFiberIso`. -/
abbrev representedStalkRingMap :
    Stacks.ringFiber (Opens.pointGrothendieckTopology (representedPoint x))
        (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos.O.obj →+*
      Stacks.ringFiber (yonedaEtaleSitePoint x)
        (smallEtaleRingedTopos B S hS (representedSpace T)).O.obj :=
  Stacks.Sheaves.StalkPullback.stalkRingMap
    (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom
      B S hS T).toRingedToposModulesHom
    (yonedaEtaleSitePoint x) (Opens.pointGrothendieckTopology (representedPoint x))
    (representedSheafFiberIso x)

/-- On underlying sheaves of sets, the transpose of the inverse-image form of the structure map
of `ε` is its direct-image form. -/
theorem representedZariski_homEquiv_fSharpInverseImage :
    (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom
      B S hS T).toToposHom.adj.homEquiv
        (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos.O)))
        (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos B S hS (representedSpace T)).O)))
        ((sheafCompose (SmallEtale.topology B S hS (yoneda.obj T)) (forget RingCat.{u})).map
          (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom
            B S hS T).toRingedToposModulesHom.fSharpInverseImage) =
      (sheafCompose (Opens.grothendieckTopology
        ↥(representedSchemeRepresentedZariskiRingedToposHom B S hS T))
        (forget CommRingCat.{u})).map
            (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS T).fSharp := by
  have h := Stacks.Sheaves.ToposPushforward.forget_map_commRingImageAdjunction_homEquiv
    (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS T).toToposHom
    (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos.O
    (smallEtaleRingedTopos B S hS (representedSpace T)).O
    (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS T).fSharpInverseImage
  have h2 : (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom
      B S hS T).fSharpInverseImage =
      ((Stacks.Sheaves.ToposPushforward.commRingImageAdjunction
        (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom
          B S hS T).toToposHom).homEquiv _ _).symm
        (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS T).fSharp := rfl
  rw [h2, Equiv.apply_symm_apply] at h
  exact h.symm

/-- On sections over an open `V`, the transpose of the inverse-image form of the structure map
of `ε` is the identification of `Γ(X_0, V)` with the functions on the scheme `V`. -/
theorem representedZariski_homEquiv_fSharpInverseImage_app
    (V : (representedSchemeRepresentedZariskiRingedToposHom B S hS T).Opens)
    (s : (representedSchemeRepresentedZariskiRingedToposHom
      B S hS T).zariskiRingedTopos.O.obj.obj (op V)) :
    ((representedZariskiRingedToposHomRepresentedZariskiRingedToposHom
      B S hS T).toToposHom.adj.homEquiv
        (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos.O)))
        (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos B S hS (representedSpace T)).O)))
        ((sheafCompose (SmallEtale.topology B S hS (yoneda.obj T)) (forget RingCat.{u})).map
          (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom
            B S hS T).toRingedToposModulesHom.fSharpInverseImage)).hom.app
        (op V) s = V.topIso.inv s := by
  rw [representedZariski_homEquiv_fSharpInverseImage (B := B) (S := S) (hS := hS) (T := T)]
  exact congrArg (fun k => k.hom.app (op V) s) (RingedToposHom.comp_fSharp_forget
    (_root_.AlgebraicGeometry.SmallEtale.toZariskiAbstractRingedToposHom (associatedBigEtaleSite B)
      (representedSchemeRepresentedZariskiRingedToposHom B S hS T) T.left.property)
    (representedSmallEtaleRingedToposHomRepresentedZariskiRingedToposHom B S hS T))

/-- **The homomorphism of stalk rings of `ε`, on germs**: the germ at `x` of a regular function
on an open `V` of the scheme underlying `T` goes to the germ at `x̄` of the same function on the
étale chart `V ⟶ yoneda.obj T`. -/
theorem representedStalkRingMap_toPresheafFiber
    (V : (representedSchemeRepresentedZariskiRingedToposHom B S hS T).Opens)
    (hv : representedPoint x ∈ V)
    (s : (representedSchemeRepresentedZariskiRingedToposHom
      B S hS T).zariskiRingedTopos.O.obj.obj (op V)) :
    representedStalkRingMap x ((Opens.pointGrothendieckTopology
      (representedPoint x)).toPresheafFiber
        V ⟨⟨hv⟩⟩
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos.O.obj s) =
      (yonedaEtaleSitePoint x).toPresheafFiber
          ((representedSchemeOpensToSmallEtaleRepresentedZariskiRingedToposHom B S hS T).obj V)
        ((representedFiberIso x).inv.app V ⟨⟨hv⟩⟩)
        (smallEtaleRingedTopos B S hS (representedSpace T)).O.obj (V.topIso.inv s) := by
  refine (Stacks.Sheaves.StalkPullback.stalkRingMap_toPresheafFiber
    (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom
      B S hS T).toRingedToposModulesHom
    (yonedaEtaleSitePoint x) (Opens.pointGrothendieckTopology (representedPoint x))
    (representedSheafFiberIso x) V ⟨⟨hv⟩⟩ s).trans ?_
  have hg := types_congr_hom (toPresheafFiber_sheafFiberIsoOfAdjOfFiberIso_inv_sheafFiber_map
    (Opens.pointGrothendieckTopology (representedPoint x)) (yonedaEtaleSitePoint x)
    (representedSchemeOpensToSmallEtaleRepresentedZariskiRingedToposHom B S hS T)
      (representedFiberIso x)
    (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS T).toToposHom.adj
    (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf
      (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos.O)))
    (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (representedSpace T)).O)))
    ((sheafCompose (SmallEtale.topology B S hS (yoneda.obj T)) (forget RingCat.{u})).map
      (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom
        B S hS T).toRingedToposModulesHom.fSharpInverseImage)
    V ⟨⟨hv⟩⟩) s
  have hg' : ((yonedaEtaleSitePoint x).sheafFiber (A := Type u)).map
        ((sheafCompose (SmallEtale.topology B S hS (yoneda.obj T)) (forget RingCat.{u})).map
          (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom
            B S hS T).toRingedToposModulesHom.fSharpInverseImage)
        ((representedSheafFiberIso x).hom.app
          (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf
            (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos.O)))
          ((Opens.pointGrothendieckTopology (representedPoint x)).toPresheafFiber V ⟨⟨hv⟩⟩
            (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf
              (representedSchemeRepresentedZariskiRingedToposHom
                B S hS T).zariskiRingedTopos.O))).obj s)) =
      (yonedaEtaleSitePoint x).toPresheafFiber
          ((representedSchemeOpensToSmallEtaleRepresentedZariskiRingedToposHom B S hS T).obj V)
        ((representedFiberIso x).inv.app V ⟨⟨hv⟩⟩)
        (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos B S hS (representedSpace T)).O))).obj (V.topIso.inv s) :=
    hg.trans (congrArg ((yonedaEtaleSitePoint x).toPresheafFiber
      ((representedSchemeOpensToSmallEtaleRepresentedZariskiRingedToposHom B S hS T).obj V)
        ((representedFiberIso x).inv.app V ⟨⟨hv⟩⟩)
      (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS (representedSpace T)).O))).obj)
      (representedZariski_homEquiv_fSharpInverseImage_app V s))
  refine (congrArg (fun z => (Stacks.commRingPresheafFiberIso (yonedaEtaleSitePoint x)
      (smallEtaleRingedTopos B S hS (representedSpace T)).O.obj).hom.hom
    (Stacks.Sheaves.StalkTransport.ringStalkComparison (yonedaEtaleSitePoint x)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS
        (representedSpace T)).O)) z))
    hg').trans ?_
  refine (congrArg (Stacks.commRingPresheafFiberIso (yonedaEtaleSitePoint x)
      (smallEtaleRingedTopos B S hS (representedSpace T)).O.obj).hom.hom
    (Stacks.Sheaves.StalkTransport.ringStalkComparison_ringGerm (yonedaEtaleSitePoint x)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS
        (representedSpace T)).O))
      _ _ _)).trans ?_
  exact Stacks.commRingPresheafFiberIso_hom_toPresheafFiber (yonedaEtaleSitePoint x)
    (smallEtaleRingedTopos B S hS (representedSpace T)).O.obj
    ((representedSchemeOpensToSmallEtaleRepresentedZariskiRingedToposHom B S hS T).obj V)
        ((representedFiberIso x).inv.app V ⟨⟨hv⟩⟩)
    (V.topIso.inv s)

/-- **The homomorphism of stalk rings of `ε` is the canonical map of Stacks 05VP.**  Read
through the identification of the fibre at `x` of `𝒪_{X_0}` with the local ring `𝒪_{X_0, x}` and
of the fibre at `x̄` of `𝒪_X` with the étale local ring, it is the canonical map
`𝒪_{X_0, x} ⟶ 𝒪_{X, x̄}` of the identity chart. -/
theorem pointStalkRingEquiv_representedStalkRingMap
    (w : (representedSchemeRepresentedZariskiRingedToposHom B S hS T).presheaf.stalk
      (representedPoint x)) :
    pointStalkRingEquiv B S hS (representedSpace T) x
        (representedStalkRingMap x ((Opens.pointFiberStalkIso (representedPoint x)
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T).presheaf).inv w)) =
      chartLocalRingToEtaleLocalRing B S hS (yoneda.obj T)
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T)
            (yonedaIdentityNeighborhood T x) w := by
  obtain ⟨V₀, hv, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ w
  let V : (representedSchemeRepresentedZariskiRingedToposHom B S hS T).Opens := V₀
  have h1 : (Opens.pointFiberStalkIso (representedPoint x)
    (representedSchemeRepresentedZariskiRingedToposHom B S hS T).presheaf).inv
      ((representedSchemeRepresentedZariskiRingedToposHom B S hS T).presheaf.germ V
        (representedPoint x) hv s) =
      (Opens.pointGrothendieckTopology (representedPoint x)).toPresheafFiber V ⟨⟨hv⟩⟩
        (representedSchemeRepresentedZariskiRingedToposHom B S hS T).presheaf s :=
    ConcreteCategory.congr_hom (Opens.germ_pointFiberStalkInv (representedPoint x) _ V hv) s
  refine (congrArg (fun z => pointStalkRingEquiv B S hS (representedSpace T) x
    (representedStalkRingMap x z)) h1).trans ?_
  refine (congrArg (pointStalkRingEquiv B S hS (representedSpace T) x)
    (representedStalkRingMap_toPresheafFiber x V hv s)).trans ?_
  refine (pointStalkRingEquiv_germ_neighborhood B S hS (representedSpace T) x
    (chartOpenNeighborhood B S hS (yonedaIdentityNeighborhood T x) V hv) (V.topIso.inv s)).trans ?_
  exact (chartLocalRingToEtaleLocalRing_germ_open B S hS
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T)
      (yonedaIdentityNeighborhood T x) V hv s).symm

/-- The identification of the fibre of `𝒪_{X_0}` at the point of the site of opens attached to
`x` with the local ring `𝒪_{X_0, x}`. -/
abbrev representedZariskiFiberRingEquiv :
    Stacks.ringFiber (Opens.pointGrothendieckTopology (representedPoint x))
        (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos.O.obj ≃+*
      (representedSchemeRepresentedZariskiRingedToposHom B S hS T).presheaf.stalk
          (representedPoint x) :=
  (Opens.pointFiberStalkIso (representedPoint x)
    (representedSchemeRepresentedZariskiRingedToposHom B S hS T).presheaf).commRingCatIsoToRingEquiv

/-- **The fibre of an `𝒪_{X_0}`-module at the point of the site of opens attached to `x` is its
stalk at `x`**, with scalars restricted along
`AlgebraicGeometry.Space.representedZariskiFiberRingEquiv`. -/
def representedZariskiFiberStalkIso :
    Stacks.sheafModuleFiberOfCommRing (Opens.pointGrothendieckTopology (representedPoint x))
        (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos.O ≅
      Stacks.ModuleSkyscraper.modulesStalkFunctor
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T)
          (representedPoint x) ⋙
        ModuleCat.restrictScalars (representedZariskiFiberRingEquiv x).toRingHom :=
  Opens.moduleFiberStalkFunctorIsoOfCommRing (representedPoint x)
      (representedSchemeRepresentedZariskiRingedToposHom B S hS T).sheaf ≪≫
    Functor.isoWhiskerLeft _ (ModuleCat.restrictScalarsComp'.{u}
      (representedZariskiFiberRingEquiv x).toRingHom
      (AlgebraicGeometry.ringCatStalkRingEquiv (representedPoint x)).symm.toRingHom
      (Opens.commRingFiberStalkHom (representedPoint x)
        (representedSchemeRepresentedZariskiRingedToposHom B S hS T).sheaf).hom
      (RingHom.ext fun z =>
        ((SemilinearStalk.commStalkIso _ _).ringCatIsoToRingEquiv.symm_apply_apply _).symm.trans
          (congrArg (SemilinearStalk.commStalkIso _ _).ringCatIsoToRingEquiv.symm
            (ConcreteCategory.congr_hom (Opens.commRingFiberStalkHom_comp_commStalkIso
              (representedPoint x)
              (representedSchemeRepresentedZariskiRingedToposHom B S hS T).sheaf) z)))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (AffineRelativeTorAmplitude.modulesStalkRestrictScalarsFunctorIso
      (representedSchemeRepresentedZariskiRingedToposHom B S hS T) (representedPoint x)) _

/-- **The homomorphism `𝒪_{X_0, x} ⟶ (𝒪_X)_{x̄}`** along which the stalk of `ε^*` is a base
change: the canonical map of Stacks 05VP of the identity chart, read in the fibre at `x̄`. -/
abbrev representedStalkBaseChangeMap :
    (representedSchemeRepresentedZariskiRingedToposHom B S hS T).presheaf.stalk
        (representedPoint x) →+*
      Stacks.ringFiber (yonedaEtaleSitePoint x)
        (smallEtaleRingedTopos B S hS (representedSpace T)).O.obj :=
  (pointStalkRingEquiv B S hS (representedSpace T) x).symm.toRingHom.comp
    (chartLocalRingToEtaleLocalRing B S hS (yoneda.obj T)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T) (yonedaIdentityNeighborhood T x))

/-- The homomorphism of stalk rings of `ε` is
`AlgebraicGeometry.Space.representedStalkBaseChangeMap` precomposed with the identification of the
fibre with the local ring. -/
theorem representedStalkBaseChangeMap_comp :
    (representedStalkBaseChangeMap x).comp (representedZariskiFiberRingEquiv x).toRingHom =
      representedStalkRingMap x := by
  refine RingHom.ext fun z => ?_
  have h := pointStalkRingEquiv_representedStalkRingMap x
    ((representedZariskiFiberRingEquiv x) z)
  have hz : (Opens.pointFiberStalkIso (representedPoint x)
      (representedSchemeRepresentedZariskiRingedToposHom B S hS T).presheaf).inv
          ((representedZariskiFiberRingEquiv x) z) = z :=
    (representedZariskiFiberRingEquiv x).symm_apply_apply z
  rw [hz] at h
  exact (pointStalkRingEquiv B S hS (representedSpace T) x).symm_apply_eq.2 h.symm

/-- **The stalk of `ε^*` at `x̄` is a base change of the stalk at `x`** (Stacks 05V5 for `ε`):
`(ε^*M)_{x̄} ≅ M_x ⊗_{𝒪_{X_0, x}} 𝒪_{X, x̄}`, naturally in the `𝒪_{X_0}`-module `M`. -/
def representedZariskiPullbackStalkIso :
    representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS T ⋙
        Stacks.sheafModuleFiberOfCommRing (yonedaEtaleSitePoint x)
          (smallEtaleRingedTopos B S hS (representedSpace T)).O ≅
      Stacks.ModuleSkyscraper.modulesStalkFunctor
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T)
          (representedPoint x) ⋙
        ModuleCat.extendScalars (representedStalkBaseChangeMap x) :=
  Functor.isoWhiskerRight (eqToIso
      (RingedToposHom.pullbackModules_eq_pullbackModules_toRingedToposModulesHom
        (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS T))) _ ≪≫
    Stacks.Sheaves.StalkPullback.stalkFunctorIso
      (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom
        B S hS T).toRingedToposModulesHom
      (yonedaEtaleSitePoint x) (Opens.pointGrothendieckTopology (representedPoint x))
      (representedSheafFiberIso x) ≪≫
    Functor.isoWhiskerRight (representedZariskiFiberStalkIso x) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (eqToIso (congrArg (fun φ => ModuleCat.restrictScalars
          (representedZariskiFiberRingEquiv x).toRingHom ⋙ ModuleCat.extendScalars φ)
          (representedStalkBaseChangeMap_comp x).symm) ≪≫
        ModuleCat.restrictExtendScalarsCompIso (RingHom.id _) (representedStalkBaseChangeMap x)
          (representedZariskiFiberRingEquiv x) ≪≫
        Functor.isoWhiskerRight (ModuleCat.restrictScalarsId _) _ ≪≫ Functor.leftUnitor _)

/-- Naturality of `AlgebraicGeometry.Space.representedZariskiPullbackStalkIso`, componentwise. -/
theorem representedZariskiPullbackStalkIso_naturality
    {M N : (representedSchemeRepresentedZariskiRingedToposHom B S hS T).Modules} (φ : M ⟶ N) :
    (Stacks.sheafModuleFiberOfCommRing (yonedaEtaleSitePoint x)
          (smallEtaleRingedTopos B S hS (representedSpace T)).O).map
        ((representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS T).map φ) ≫
      ((representedZariskiPullbackStalkIso x).app N).hom =
    ((representedZariskiPullbackStalkIso x).app M).hom ≫
      (ModuleCat.extendScalars (representedStalkBaseChangeMap x)).map
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T)
          (representedPoint x)).map φ) :=
  (representedZariskiPullbackStalkIso x).hom.naturality φ

/-- The stalk complex at `x̄` of `ε^*K` is the base change along `𝒪_{X, x} ⟶ 𝒪_{X, x̄}` of the
stalk complex of `K` at `x`. -/
def representedZariskiPullbackStalkComplexIso
    (K : CochainComplex (representedSchemeRepresentedZariskiRingedToposHom B S hS T).Modules ℤ) :
    ((Stacks.sheafModuleFiberOfCommRing (yonedaEtaleSitePoint x)
          (smallEtaleRingedTopos B S hS (representedSpace T)).O).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((representedZariskiModulePullbackRepresentedZariskiPullbackExact
          B S hS T).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ≅
      ((ModuleCat.extendScalars (representedStalkBaseChangeMap x)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((Stacks.ModuleSkyscraper.modulesStalkFunctor
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T)
          (representedPoint x)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (representedZariskiPullbackStalkIso x).app (K.X i))
    (fun i j _ => (representedZariskiPullbackStalkIso_naturality x (K.d i j)).symm)

end AlgebraicGeometry.Space

end
