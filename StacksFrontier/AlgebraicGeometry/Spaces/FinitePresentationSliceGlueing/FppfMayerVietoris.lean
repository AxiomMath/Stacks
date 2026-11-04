module

public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.MayerVietorisSquare
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Subfunctor.Image
public import Mathlib.CategoryTheory.Subterminal
public import StacksFrontier.AlgebraicGeometry.Full.Square
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraicityOnBaseCover
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeLocalCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSlice
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfOverTypeSheafification
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSliceGlueing.GluedPresheaf

/-!
# Coverings of the base of the big fppf site by two opens

Invariance of finite presentation under isomorphisms of arrows, the two-member Zariski covering
of the base cut out by two jointly surjective open immersions, the covering sieve and the
Mayer--Vietoris square of the big fppf site of `S` attached to them, the glueing of sections of
an fppf sheaf along that square, and the faithfulness of the comparison functor from the
algebraic spaces of finite presentation over the base into the `2`-fibre product
`FP_U ×_{FP_V} FP_W` (Stacks 0E8Z).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

namespace Space

/-! ### Finite presentation and isomorphisms of arrows -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (f' : X' ⟶ Y')

/-- **Being locally of finite presentation depends only on the arrow up to isomorphism**, by the
two invariance statements of the every-étale-chart condition of Stacks 03MJ. -/
theorem isLocallyOfFinitePresentation_of_arrowIso (e₁ : X ⟶ X') (e₂ : Y ⟶ Y') [IsIso e₁]
    [IsIso e₂] (w : e₁ ≫ f' = f ≫ e₂) (hf : IsLocallyOfFinitePresentation B S hS f) :
    IsLocallyOfFinitePresentation B S hS f' := by
  rw [show f' = inv e₁ ≫ f ≫ e₂ from (IsIso.eq_inv_comp _).2 w]
  exact (holdsOnEveryEtaleChart_iso_comp_iff B S hS _ (inv e₁) (f ≫ e₂)).2
    ((holdsOnEveryEtaleChart_comp_iso_iff B S hS _ f e₂).2 hf)

/-- **Being of finite presentation depends only on the arrow up to isomorphism**, each of its
three conjuncts being invariant. -/
theorem isFinitePresentation_of_arrowIso (e₁ : X ⟶ X') (e₂ : Y ⟶ Y') [IsIso e₁] [IsIso e₂]
    (w : e₁ ≫ f' = f ≫ e₂) (hf : IsFinitePresentation B S hS f) :
    IsFinitePresentation B S hS f' :=
  ⟨isLocallyOfFinitePresentation_of_arrowIso B S hS f f' e₁ e₂ w hf.1,
    isQuasiCompact_of_arrowIso B S hS f f' e₁ e₂ w hf.2.1,
    isQuasiSeparated_of_arrowIso B S hS f f' e₁ e₂ w hf.2.2⟩

/-- A cartesian square over a monomorphism `p` transports finite presentation of its left edge
to the base change along the inclusion of the range of `p`. -/
theorem isFinitePresentation_pullback_snd_range {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {g : F ⟶ H} {p : G ⟶ H} [Mono p] {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a : P ⟶ F}
    {b : P ⟶ G} (h : IsPullback a b g p) (hb : IsFinitePresentation B S hS b) :
    IsFinitePresentation B S hS (pullback.snd g (Subfunctor.range p).ι) := by
  have h' := h.of_toRange
  have hb' : IsFinitePresentation B S hS (b ≫ Subfunctor.toRange p) :=
    isFinitePresentation_of_arrowIso B S hS b (b ≫ Subfunctor.toRange p) (𝟙 _)
      (Subfunctor.toRange p) (by simp) hb
  refine isFinitePresentation_of_arrowIso B S hS (b ≫ Subfunctor.toRange p) _
    (h'.isoIsPullback _ _ (IsPullback.of_hasPullback g (Subfunctor.range p).ι)).hom (𝟙 _) ?_ hb'
  rw [Category.comp_id]
  exact h'.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback g (Subfunctor.range p).ι)

/-! ### The two-member Zariski covering of the base -/

variable {Z U W : BigFppfOver B S hS}

/-- The two-member family of subfunctors of the representable presheaf of `Z` cut out by two
morphisms `jU : U ⟶ Z` and `jW : W ⟶ Z`, indexed by `ULift.{u} Bool`. -/
noncomputable def rangePair (jU : U ⟶ Z) (jW : W ⟶ Z) :
    ULift.{u} Bool → Subfunctor (yoneda.obj Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  fun i => if i.down then Subfunctor.range (yoneda.map jU) else Subfunctor.range (yoneda.map jW)

/-- The member of `AlgebraicGeometry.Space.rangePair` at `true` is the range of `jU`. -/
@[simp]
theorem rangePair_true (jU : U ⟶ Z) (jW : W ⟶ Z) :
    rangePair B S hS jU jW ⟨true⟩ = Subfunctor.range (yoneda.map jU) :=
  rfl

/-- The member of `AlgebraicGeometry.Space.rangePair` at `false` is the range of `jW`. -/
@[simp]
theorem rangePair_false (jU : U ⟶ Z) (jW : W ⟶ Z) :
    rangePair B S hS jU jW ⟨false⟩ = Subfunctor.range (yoneda.map jW) :=
  rfl

/-- Each member of `AlgebraicGeometry.Space.rangePair` is an open subspace of the representable
presheaf of `Z` when the two morphisms are open immersions. -/
theorem isOpenSubspace_rangePair {jU : U ⟶ Z} {jW : W ⟶ Z}
    (hjU : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map jU))
    (hjW : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map jW))
    (i : ULift.{u} Bool) : IsOpenSubspace B S hS (rangePair B S hS jU jW i) := by
  rcases i with ⟨_ | _⟩
  · exact isOpenSubspace_range_of_isOpenImmersion W (yoneda.map jW)
      (isOpenImmersion_yoneda_map B S hS jW hjW)
  · exact isOpenSubspace_range_of_isOpenImmersion U (yoneda.map jU)
      (isOpenImmersion_yoneda_map B S hS jU hjU)

/-- **Two open immersions generating a covering sieve give a Zariski covering of the
representable presheaf of their target.** Local surjectivity of the map from the coproduct is the
covering sieve itself: a morphism in it factors through one of the two, which is exactly a
section of the corresponding range subfunctor. -/
theorem isZariskiCover_rangePair {jU : U ⟶ Z} {jW : W ⟶ Z}
    (hjU : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map jU))
    (hjW : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map jW))
    (hcov : Sieve.ofTwoArrows jU jW ∈ BigFppfOver.topology B S hS Z) :
    IsZariskiCover B S hS (ULift.{u} Bool) (rangePair B S hS jU jW) := by
  refine ⟨isOpenSubspace_rangePair B S hS hjU hjW, ⟨fun {Y} x => ?_⟩⟩
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    ((BigFppfOver.topology B S hS).pullback_stable x hcov)
  rintro T g hg
  obtain ⟨(_ | _), a, ha⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
  · refine ⟨(Sigma.ι (fun i => (rangePair B S hS jU jW i).toFunctor) ⟨true⟩).app (op T)
      ⟨g ≫ x, ⟨(a : T ⟶ U), ha.symm⟩⟩, ?_⟩
    exact ConcreteCategory.congr_hom (NatTrans.congr_app
      (Sigma.ι_desc (fun i => (rangePair B S hS jU jW i).ι) ⟨true⟩) (op T)) _
  · refine ⟨(Sigma.ι (fun i => (rangePair B S hS jU jW i).toFunctor) ⟨false⟩).app (op T)
      ⟨g ≫ x, ⟨(a : T ⟶ W), ha.symm⟩⟩, ?_⟩
    exact ConcreteCategory.congr_hom (NatTrans.congr_app
      (Sigma.ι_desc (fun i => (rangePair B S hS jU jW i).ι) ⟨false⟩) (op T)) _

end Space

namespace FinitePresentationSpacesOver

open CategoryTheory.SubterminalGlueing

attribute [local instance] BigFppfOver.hasSheafify_type

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Z U W V : BigFppfOver B S hS}

/-! ### Coverings of the base by two opens -/

/-- Two jointly surjective open immersions onto an object of the big fppf category over `S`
generate a covering sieve of its fppf topology. This is
`AlgebraicGeometry.BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion` for a two-element
family. -/
theorem ofTwoArrows_mem_topology (jU : U ⟶ Z) (jW : W ⟶ Z)
    (hjU : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map jU))
    (hjW : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map jW))
    (hcov : ∀ x : (BigFppfOver.toScheme B S hS).obj Z,
      x ∈ Set.range ((BigFppfOver.toScheme B S hS).map jU) ∨
        x ∈ Set.range ((BigFppfOver.toScheme B S hS).map jW)) :
    Sieve.ofTwoArrows jU jW ∈ BigFppfOver.topology B S hS Z :=
  BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS (X := pairFunction U W)
    (fun k => WalkingPair.casesOn k jU jW) (by rintro (_ | _) <;> assumption)
    (fun x => by
      rcases hcov x with h | h
      exacts [⟨WalkingPair.left, h⟩, ⟨WalkingPair.right, h⟩])

variable (hZ : IsTerminal Z) {jU : U ⟶ Z} {jW : W ⟶ Z} [Mono jU] [Mono jW] {iU : V ⟶ U}
  {iW : V ⟶ W} (hV : IsPullback iU iW jU jW)

/-! ### The Mayer--Vietoris square of the fppf site -/

/-- **The Mayer--Vietoris square of an object of the big fppf site of `S` relative to a
two-element covering of the base.** If `jU : U ⟶ Z` and `jW : W ⟶ Z` are monomorphisms onto a
terminal object of the site which generate a covering sieve, and `V` is their intersection, then
for every object `X` the square with vertices `V ⨯ X`, `U ⨯ X`, `W ⨯ X` and `X` is a
Mayer--Vietoris square for the fppf topology. -/
noncomputable def mayerVietorisSquare
    (hcov : Sieve.ofTwoArrows jU jW ∈ BigFppfOver.topology B S hS Z)
    (X : BigFppfOver B S hS) : (BigFppfOver.topology B S hS).MayerVietorisSquare :=
  (BigFppfOver.topology B S hS).mayerVietorisSquareProd hZ hV hcov X

/-- The sheaf condition of an algebraic space over `S` at the Mayer--Vietoris square of an object
`X` relative to a two-element covering of the base: the sections over `X` are the fibre product
of the sections over `U ⨯ X` and over `W ⨯ X` above the sections over `V ⨯ X`. -/
theorem sheafCondition_mayerVietorisSquare
    (hcov : Sieve.ofTwoArrows jU jW ∈ BigFppfOver.topology B S hS Z)
    (X : BigFppfOver B S hS) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) :
    (mayerVietorisSquare B S hS hZ hV hcov X).SheafCondition F :=
  GrothendieckTopology.MayerVietorisSquare.sheafCondition_of_sheaf _ ⟨F, hF⟩

section Glue

variable (hcov : Sieve.ofTwoArrows jU jW ∈ BigFppfOver.topology B S hS Z)
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) (T : BigFppfOver B S hS)

include hZ hV hcov hF in
/-- **A section of an fppf sheaf over `T` is determined by its restrictions to `U ⨯ T` and to
`W ⨯ T`**, by the sheaf condition at the Mayer--Vietoris square of `T`. -/
theorem sheafSection_ext_prod {x y : F.obj (op T)}
    (h₁ : F.map (prod.snd : U ⨯ T ⟶ T).op x = F.map (prod.snd : U ⨯ T ⟶ T).op y)
    (h₂ : F.map (prod.snd : W ⨯ T ⟶ T).op x = F.map (prod.snd : W ⨯ T ⟶ T).op y) : x = y :=
  (sheafCondition_mayerVietorisSquare B S hS hZ hV hcov T hF).ext h₁ h₂

include hZ hV hcov hF in
/-- **Two sections of an fppf sheaf over `U ⨯ T` and over `W ⨯ T` which agree over `V ⨯ T` glue
to a section over `T`**, by the sheaf condition at the Mayer--Vietoris square of `T`. -/
noncomputable def glueProd (a : F.obj (op (U ⨯ T))) (b : F.obj (op (W ⨯ T)))
    (hab : F.map (prod.map iU (𝟙 T)).op a = F.map (prod.map iW (𝟙 T)).op b) : F.obj (op T) :=
  (sheafCondition_mayerVietorisSquare B S hS hZ hV hcov T hF).glue a b hab

include hZ hV hcov hF in
/-- The restriction to `U ⨯ T` of a glued section is the first of the two sections glued. -/
@[simp]
theorem map_prod_snd_op_glueProd_left (a : F.obj (op (U ⨯ T))) (b : F.obj (op (W ⨯ T)))
    (hab : F.map (prod.map iU (𝟙 T)).op a = F.map (prod.map iW (𝟙 T)).op b) :
    F.map (prod.snd : U ⨯ T ⟶ T).op (glueProd B S hS hZ hV hcov hF T a b hab) = a :=
  GrothendieckTopology.MayerVietorisSquare.SheafCondition.map_f₂₄_op_glue
    (sheafCondition_mayerVietorisSquare B S hS hZ hV hcov T hF) a b hab

include hZ hV hcov hF in
/-- The restriction to `W ⨯ T` of a glued section is the second of the two sections glued. -/
@[simp]
theorem map_prod_snd_op_glueProd_right (a : F.obj (op (U ⨯ T))) (b : F.obj (op (W ⨯ T)))
    (hab : F.map (prod.map iU (𝟙 T)).op a = F.map (prod.map iW (𝟙 T)).op b) :
    F.map (prod.snd : W ⨯ T ⟶ T).op (glueProd B S hS hZ hV hcov hF T a b hab) = b :=
  GrothendieckTopology.MayerVietorisSquare.SheafCondition.map_f₃₄_op_glue
    (sheafCondition_mayerVietorisSquare B S hS hZ hV hcov T hF) a b hab

end Glue

omit [Mono jU] [Mono jW] in
/-- **The comparison isomorphism of the square, read in the slice of presheaves.** The
comparison of `AlgebraicGeometry.FinitePresentationSpacesOver.baseChangeSquareIso` is the
comparison of `CategoryTheory.Over.pullbackSquareIso` of the Yoneda image of the square. -/
theorem baseChangeSquareIso_hom_app_left (w : iU ≫ jU = iW ≫ jW)
    (T : FinitePresentationSpacesOver B S hS Z) :
    (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS V)).map
        ((baseChangeSquareIso B S hS w).hom.app T) =
      (Over.pullbackSquareIso (u := yoneda.map jU) (p := yoneda.map jW)
        (q := yoneda.map iU) (v := yoneda.map iW)
        (by rw [← Functor.map_comp, ← Functor.map_comp, w])).hom.app T.obj :=
  Functor.map_preimage _ _

/-! ### Faithfulness of the comparison functor -/

include hZ hV in
/-- **A morphism into an fppf sheaf is determined by its restrictions along the products with
`U` and with `W`**, by the sheaf condition at the Mayer--Vietoris square. -/
theorem natTrans_ext_of_prod_app
    (hcov : Sieve.ofTwoArrows jU jW ∈ BigFppfOver.topology B S hS Z)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G) {α β : F ⟶ G}
    (hαU : ∀ T : BigFppfOver B S hS, α.app (op (U ⨯ T)) = β.app (op (U ⨯ T)))
    (hαW : ∀ T : BigFppfOver B S hS, α.app (op (W ⨯ T)) = β.app (op (W ⨯ T))) : α = β := by
  refine NatTrans.ext (funext fun T => ConcreteCategory.hom_ext _ _ fun x => ?_)
  have key : ∀ {P : BigFppfOver B S hS},
      (∀ T : BigFppfOver B S hS, α.app (op (P ⨯ T)) = β.app (op (P ⨯ T))) →
      G.map (prod.snd : P ⨯ T.unop ⟶ T.unop).op (α.app T x) =
        G.map (prod.snd : P ⨯ T.unop ⟶ T.unop).op (β.app T x) := fun h => by
    rw [← NatTrans.naturality_apply α, ← NatTrans.naturality_apply β,
      ConcreteCategory.congr_hom (h T.unop) _]
  exact sheafSection_ext_prod B S hS hZ hV hcov hG T.unop (key hαU) (key hαW)

include hZ hV in
/-- **A morphism of the slice over the representable presheaf of the base is determined by its
base changes to `U` and to `W`.** -/
theorem over_hom_ext_of_pullback_map_eq
    (hcov : Sieve.ofTwoArrows jU jW ∈ BigFppfOver.topology B S hS Z)
    {X Y : Over (yoneda.obj Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y.left) {f g : X ⟶ Y}
    (hfU : (Over.pullback (yoneda.map jU)).map f = (Over.pullback (yoneda.map jU)).map g)
    (hfW : (Over.pullback (yoneda.map jW)).map f = (Over.pullback (yoneda.map jW)).map g) :
    f = g := by
  refine Over.OverMorphism.ext ?_
  refine natTrans_ext_of_prod_app B S hS hZ hV hcov hY ?_ ?_
  · exact Over.app_prod_eq_of_pullback_map_eq hZ jU (isSubterminal_of_mono_isTerminal hZ jU) hfU
  · exact Over.app_prod_eq_of_pullback_map_eq hZ jW (isSubterminal_of_mono_isTerminal hZ jW) hfW

include hZ in
/-- **The comparison functor into the `2`-fibre product is faithful.** Two morphisms with the
same base changes to `U` and to `W` agree, because the target is a sheaf and the two
projections `U ⨯ T ⟶ T` and `W ⨯ T ⟶ T` form a Mayer--Vietoris square. -/
theorem faithful_glueingFunctor
    (hcov : Sieve.ofTwoArrows jU jW ∈ BigFppfOver.topology B S hS Z) :
    (glueingFunctor B S hS hV.w).Faithful where
  map_injective {X Y} {f g} h := by
    refine (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS Z)).map_injective ?_
    refine over_hom_ext_of_pullback_map_eq B S hS hZ hV hcov Y.property.1.isSheaf ?_ ?_
    · exact congrArg (fun m => (ObjectProperty.ι
        (IsFinitePresentationSpaceOver B S hS U)).map m.hom.left) h
    · exact congrArg (fun m => (ObjectProperty.ι
        (IsFinitePresentationSpaceOver B S hS W)).map m.hom.right) h

end FinitePresentationSpacesOver

end AlgebraicGeometry

end
