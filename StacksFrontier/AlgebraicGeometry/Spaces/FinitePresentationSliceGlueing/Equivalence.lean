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
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSliceGlueing.FppfMayerVietoris

/-!
# Glueing algebraic spaces of finite presentation along a covering by two opens

The comparison functor from the algebraic spaces of finite presentation over the base of the big
fppf site of `S` to the `2`-fibre product `FP_U ×_{FP_V} FP_W` attached to a covering of the base
by two opens is full; the glueing functor out of that `2`-fibre product lands in algebraic spaces
of finite presentation over the base; and the comparison functor is an equivalence, with
explicit unit and counit (Stacks 0E8Z).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

namespace FinitePresentationSpacesOver

open CategoryTheory.SubterminalGlueing

attribute [local instance] BigFppfOver.hasSheafify_type

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Z U W V : BigFppfOver B S hS}

variable (hZ : IsTerminal Z) {jU : U ⟶ Z} {jW : W ⟶ Z} [Mono jU] [Mono jW] {iU : V ⟶ U}
  {iW : V ⟶ W} (hV : IsPullback iU iW jU jW)

/-! ### Fullness of the comparison functor -/

section Full

omit hZ hV [Mono jU] [Mono jW] in
/-- The inclusion of the algebraic spaces of finite presentation into the slice of presheaves
takes a base-changed morphism to the base change of the underlying morphism. -/
@[simp]
theorem ι_map_baseChange_map {X' Y' : BigFppfOver B S hS} (j : X' ⟶ Y')
    {F G : FinitePresentationSpacesOver B S hS Y'} (f : F ⟶ G) :
    (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS X')).map
        ((baseChange B S hS j).map f) =
      (Over.pullback (yoneda.map j)).map
        ((ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS Y')).map f) :=
  rfl

omit hZ hV [Mono jU] [Mono jW] in
/-- The comparison morphism of the image of an object under the comparison functor is the
component of the square isomorphism. -/
@[simp]
theorem glueingFunctor_obj_hom (w : iU ≫ jU = iW ≫ jW)
    (T : FinitePresentationSpacesOver B S hS Z) :
    ((glueingFunctor B S hS w).obj T).obj.hom = (baseChangeSquareIso B S hS w).hom.app T :=
  rfl

omit hZ hV [Mono jU] [Mono jW] in
/-- The first component of the image of a morphism under the comparison functor is its base
change to `U`. -/
@[simp]
theorem glueingFunctor_map_hom_left (w : iU ≫ jU = iW ≫ jW)
    {F G : FinitePresentationSpacesOver B S hS Z} (f : F ⟶ G) :
    ((glueingFunctor B S hS w).map f).hom.left = (baseChange B S hS jU).map f :=
  rfl

omit hZ hV [Mono jU] [Mono jW] in
/-- The second component of the image of a morphism under the comparison functor is its base
change to `W`. -/
@[simp]
theorem glueingFunctor_map_hom_right (w : iU ≫ jU = iW ≫ jW)
    {F G : FinitePresentationSpacesOver B S hS Z} (f : F ⟶ G) :
    ((glueingFunctor B S hS w).map f).hom.right = (baseChange B S hS jW).map f :=
  rfl

variable {X Y : Over (yoneda.obj Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
  (mU : (Over.pullback (yoneda.map jU)).obj X ⟶ (Over.pullback (yoneda.map jU)).obj Y)
  (mW : (Over.pullback (yoneda.map jW)).obj X ⟶ (Over.pullback (yoneda.map jW)).obj Y)

omit hZ hV [Mono jU] [Mono jW] in
/-- Restricting a section along the projection from the product with `U'` commutes with
restricting it along a morphism of the base. -/
theorem map_prod_snd_op_comp {U' : BigFppfOver B S hS}
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) {T T' : (BigFppfOver B S hS)ᵒᵖ} (g : T ⟶ T')
    (z : F.obj T) :
    F.map (prod.snd : U' ⨯ T'.unop ⟶ T'.unop).op (F.map g z) =
      F.map (prod.map (𝟙 U') g.unop).op (F.map (prod.snd : U' ⨯ T.unop ⟶ T.unop).op z) := by
  simp only [← Functor.map_comp_apply]
  exact congrArg (fun h => F.map h z) (Quiver.Hom.unop_inj (by simp))

omit hV [Mono jU] [Mono jW] in
/-- The section of `Y` over `U' ⨯ T` attached to a section of `X` over `T` by a base change to
`U'` is natural in `T`. -/
theorem pullbackSectionsMap_prod_naturality {U' : BigFppfOver B S hS} (jU' : U' ⟶ Z) [Mono jU']
    (m : (Over.pullback (yoneda.map jU')).obj X ⟶ (Over.pullback (yoneda.map jU')).obj Y)
    {T T' : (BigFppfOver B S hS)ᵒᵖ} (g : T ⟶ T') (x : X.left.obj T) :
    Y.left.map (prod.map (𝟙 U') g.unop).op
        (Over.pullbackSectionsMap hZ jU' (isSubterminal_of_mono_isTerminal hZ jU') m
          ⟨prod.fst⟩ (X.left.map (prod.snd : U' ⨯ T.unop ⟶ T.unop).op x)) =
      Over.pullbackSectionsMap hZ jU' (isSubterminal_of_mono_isTerminal hZ jU') m ⟨prod.fst⟩
        (X.left.map (prod.snd : U' ⨯ T'.unop ⟶ T'.unop).op (X.left.map g x)) := by
  rw [Over.pullbackSectionsMap_naturality hZ jU' (isSubterminal_of_mono_isTerminal hZ jU') m
      (prod.map (𝟙 U') g.unop) ⟨prod.fst⟩ ⟨prod.fst⟩,
    map_prod_snd_op_comp B S hS X.left g x]

/-- Two compatible base changes of a morphism of presheaves induce the same map on sections over
an object `T` lying over `V`. -/
private theorem pullbackSectionsMap_eq_of_hcomm
    (hcomm : (Over.pullback (yoneda.map iU)).map mU ≫
        (Over.pullbackSquareObjIso (yoneda_map_comm hV.w) Y).hom =
      (Over.pullbackSquareObjIso (yoneda_map_comm hV.w) X).hom ≫
        (Over.pullback (yoneda.map iW)).map mW)
    {T : BigFppfOver B S hS} (p : T ⟶ V) (x : X.left.obj (op T)) :
    Over.pullbackSectionsMap hZ jU (isSubterminal_of_mono_isTerminal hZ jU) mU ⟨p ≫ iU⟩ x =
      Over.pullbackSectionsMap hZ jW (isSubterminal_of_mono_isTerminal hZ jW) mW ⟨p ≫ iW⟩ x :=
  Over.pullbackSectionsMap_eq_of_comm hZ (isSubterminal_of_mono_isTerminal hZ jU)
    (isSubterminal_of_mono_isTerminal hZ jW)
    (hV.isSubterminal (isSubterminal_of_mono_isTerminal hZ jU)
      (isSubterminal_of_mono_isTerminal hZ jW)) (yoneda_map_comm hV.w) hcomm p x

include hV in
/-- **Two compatible base changes of a morphism of presheaves over the base agree over `V ⨯ T`.**
The two sections of `Y` attached to a section of `X` over `T` by the base changes to `U` and to
`W` have the same restriction to `V ⨯ T`. -/
theorem pullbackSectionsMap_restrict_eq
    (hcomm : (Over.pullback (yoneda.map iU)).map mU ≫
        (Over.pullbackSquareObjIso (yoneda_map_comm hV.w) Y).hom =
      (Over.pullbackSquareObjIso (yoneda_map_comm hV.w) X).hom ≫
        (Over.pullback (yoneda.map iW)).map mW)
    (T : BigFppfOver B S hS) (x : X.left.obj (op T)) :
    Y.left.map (prod.map iU (𝟙 T)).op
        (Over.pullbackSectionsMap hZ jU (isSubterminal_of_mono_isTerminal hZ jU) mU
          ⟨prod.fst⟩ (X.left.map (prod.snd : U ⨯ T ⟶ T).op x)) =
      Y.left.map (prod.map iW (𝟙 T)).op
        (Over.pullbackSectionsMap hZ jW (isSubterminal_of_mono_isTerminal hZ jW) mW
          ⟨prod.fst⟩ (X.left.map (prod.snd : W ⨯ T ⟶ T).op x)) := by
  have hres : ∀ {U' : BigFppfOver B S hS} (f : V ⟶ U'),
      X.left.map (prod.map f (𝟙 T)).op (X.left.map (prod.snd : U' ⨯ T ⟶ T).op x) =
        X.left.map (prod.snd : V ⨯ T ⟶ T).op x := by
    intro U' f
    have h : prod.map f (𝟙 T) ≫ (prod.snd : U' ⨯ T ⟶ T) = (prod.snd : V ⨯ T ⟶ T) := by simp
    simp only [← Functor.map_comp_apply, ← op_comp, h]
  rw [Over.pullbackSectionsMap_naturality hZ jU (isSubterminal_of_mono_isTerminal hZ jU) mU
      (prod.map iU (𝟙 T)) ⟨prod.fst⟩ ⟨(prod.fst : V ⨯ T ⟶ V) ≫ iU⟩,
    Over.pullbackSectionsMap_naturality hZ jW (isSubterminal_of_mono_isTerminal hZ jW) mW
      (prod.map iW (𝟙 T)) ⟨prod.fst⟩ ⟨(prod.fst : V ⨯ T ⟶ V) ≫ iW⟩,
    hres iU, hres iW]
  exact pullbackSectionsMap_eq_of_hcomm B S hS hZ hV mU mW hcomm prod.fst _

variable (hcov : Sieve.ofTwoArrows jU jW ∈ BigFppfOver.topology B S hS Z)
  (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y.left)
  (hcomm : (Over.pullback (yoneda.map iU)).map mU ≫
      (Over.pullbackSquareObjIso (yoneda_map_comm hV.w) Y).hom =
    (Over.pullbackSquareObjIso (yoneda_map_comm hV.w) X).hom ≫
      (Over.pullback (yoneda.map iW)).map mW)

include hZ hV hcov hY hcomm in
/-- **The morphism of presheaves over the base glued from two compatible base-changed
morphisms.** Over `U ⨯ T` it is the first datum and over `W ⨯ T` the second; they agree over
`V ⨯ T`, so the sheaf condition at the Mayer--Vietoris square of `T` glues them. -/
noncomputable def glueingFullHom : X.left ⟶ Y.left where
  app T := ↾fun x =>
    glueProd B S hS hZ hV hcov hY T.unop
      (Over.pullbackSectionsMap hZ jU (isSubterminal_of_mono_isTerminal hZ jU) mU ⟨prod.fst⟩
        (X.left.map (prod.snd : U ⨯ T.unop ⟶ T.unop).op x))
      (Over.pullbackSectionsMap hZ jW (isSubterminal_of_mono_isTerminal hZ jW) mW ⟨prod.fst⟩
        (X.left.map (prod.snd : W ⨯ T.unop ⟶ T.unop).op x))
      (pullbackSectionsMap_restrict_eq B S hS hZ hV mU mW hcomm T.unop x)
  naturality T T' g := ConcreteCategory.hom_ext _ _ fun x => by
    simp only [types_comp_apply, TypeCat.ofHom_apply]
    refine sheafSection_ext_prod B S hS hZ hV hcov hY T'.unop ?_ ?_
    · rw [map_prod_snd_op_glueProd_left, map_prod_snd_op_comp B S hS Y.left g,
        map_prod_snd_op_glueProd_left,
        pullbackSectionsMap_prod_naturality B S hS hZ jU mU g x]
    · rw [map_prod_snd_op_glueProd_right, map_prod_snd_op_comp B S hS Y.left g,
        map_prod_snd_op_glueProd_right,
        pullbackSectionsMap_prod_naturality B S hS hZ jW mW g x]

include hZ hV hcov hY hcomm in
/-- The glued morphism is, on sections, the glueing of the two base-changed data. -/
@[simp]
theorem glueingFullHom_app_apply (T : (BigFppfOver B S hS)ᵒᵖ) (x : X.left.obj T) :
    (glueingFullHom B S hS hZ hV mU mW hcov hY hcomm).app T x =
      glueProd B S hS hZ hV hcov hY T.unop
        (Over.pullbackSectionsMap hZ jU (isSubterminal_of_mono_isTerminal hZ jU) mU ⟨prod.fst⟩
          (X.left.map (prod.snd : U ⨯ T.unop ⟶ T.unop).op x))
        (Over.pullbackSectionsMap hZ jW (isSubterminal_of_mono_isTerminal hZ jW) mW ⟨prod.fst⟩
          (X.left.map (prod.snd : W ⨯ T.unop ⟶ T.unop).op x))
        (pullbackSectionsMap_restrict_eq B S hS hZ hV mU mW hcomm T.unop x) :=
  rfl

include hZ hV hcov hY hcomm in
/-- **Over an object lying over `U` the glued morphism is the first datum.** -/
theorem glueingFullHom_app_eq_left (T : (BigFppfOver B S hS)ᵒᵖ) (hT : Nonempty (T.unop ⟶ U))
    (x : X.left.obj T) :
    (glueingFullHom B S hS hZ hV mU mW hcov hY hcomm).app T x =
      Over.pullbackSectionsMap hZ jU (isSubterminal_of_mono_isTerminal hZ jU) mU hT x := by
  obtain ⟨q⟩ := hT
  refine sheafSection_ext_prod B S hS hZ hV hcov hY T.unop ?_ ?_
  · rw [glueingFullHom_app_apply, map_prod_snd_op_glueProd_left,
      Over.pullbackSectionsMap_naturality hZ jU (isSubterminal_of_mono_isTerminal hZ jU) mU
        (prod.snd : U ⨯ T.unop ⟶ T.unop) ⟨q⟩ ⟨prod.fst⟩]
  · rw [glueingFullHom_app_apply, map_prod_snd_op_glueProd_right,
      Over.pullbackSectionsMap_naturality hZ jU (isSubterminal_of_mono_isTerminal hZ jU) mU
        (prod.snd : W ⨯ T.unop ⟶ T.unop) ⟨q⟩ ⟨(prod.snd : W ⨯ T.unop ⟶ T.unop) ≫ q⟩]
    exact (pullbackSectionsMap_eq_of_hcomm B S hS hZ hV mU mW hcomm
      (hV.lift ((prod.snd : W ⨯ T.unop ⟶ T.unop) ≫ q) prod.fst (hZ.hom_ext _ _)) _).symm

include hZ hV hcov hY hcomm in
/-- **Over an object lying over `W` the glued morphism is the second datum.** -/
theorem glueingFullHom_app_eq_right (T : (BigFppfOver B S hS)ᵒᵖ) (hT : Nonempty (T.unop ⟶ W))
    (x : X.left.obj T) :
    (glueingFullHom B S hS hZ hV mU mW hcov hY hcomm).app T x =
      Over.pullbackSectionsMap hZ jW (isSubterminal_of_mono_isTerminal hZ jW) mW hT x := by
  obtain ⟨q⟩ := hT
  refine sheafSection_ext_prod B S hS hZ hV hcov hY T.unop ?_ ?_
  · rw [glueingFullHom_app_apply, map_prod_snd_op_glueProd_left,
      Over.pullbackSectionsMap_naturality hZ jW (isSubterminal_of_mono_isTerminal hZ jW) mW
        (prod.snd : U ⨯ T.unop ⟶ T.unop) ⟨q⟩ ⟨(prod.snd : U ⨯ T.unop ⟶ T.unop) ≫ q⟩]
    exact pullbackSectionsMap_eq_of_hcomm B S hS hZ hV mU mW hcomm
      (hV.lift prod.fst ((prod.snd : U ⨯ T.unop ⟶ T.unop) ≫ q) (hZ.hom_ext _ _)) _
  · rw [glueingFullHom_app_apply, map_prod_snd_op_glueProd_right,
      Over.pullbackSectionsMap_naturality hZ jW (isSubterminal_of_mono_isTerminal hZ jW) mW
        (prod.snd : W ⨯ T.unop ⟶ T.unop) ⟨q⟩ ⟨prod.fst⟩]

include hZ hV hcov hY hcomm in
/-- The glued morphism, as a morphism of the slice over the representable presheaf of the
terminal object: the compatibility is automatic, that presheaf being terminal. -/
noncomputable def glueingFullOverHom : X ⟶ Y :=
  Over.homMk (glueingFullHom B S hS hZ hV mU mW hcov hY hcomm)
    ((hZ.isTerminalObj yoneda Z).hom_ext _ _)

/-- The base change to `U'` of the glued morphism is `m` as soon as the glued morphism restricts
to `m` on sections over objects lying over `U'`. -/
private theorem pullback_map_glueingFullOverHom_eq {U' : BigFppfOver B S hS} (jU' : U' ⟶ Z)
    [Mono jU'] (m : (Over.pullback (yoneda.map jU')).obj X ⟶ (Over.pullback (yoneda.map jU')).obj Y)
    (h : ∀ (T : (BigFppfOver B S hS)ᵒᵖ) (hT : Nonempty (T.unop ⟶ U')) (x : X.left.obj T),
      (glueingFullHom B S hS hZ hV mU mW hcov hY hcomm).app T x =
        Over.pullbackSectionsMap hZ jU' (isSubterminal_of_mono_isTerminal hZ jU') m hT x) :
    (Over.pullback (yoneda.map jU')).map
        (glueingFullOverHom B S hS hZ hV mU mW hcov hY hcomm) = m := by
  refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w m).symm))
  refine (Over.pullback_map_left_comp_fst (yoneda.map jU') _).trans ?_
  refine NatTrans.ext (funext fun T => ConcreteCategory.hom_ext _ _ fun z => ?_)
  simp only [NatTrans.comp_app, types_comp_apply, glueingFullOverHom, Over.homMk_left]
  rw [h T ⟨(pullback.snd X.hom (yoneda.map jU')).app T z⟩, Over.pullbackSectionsMap_fst]

include hZ hV hcov hY hcomm in
/-- **The base change to `U` of the glued morphism is the first datum.** -/
theorem pullback_map_glueingFullOverHom_left :
    (Over.pullback (yoneda.map jU)).map
        (glueingFullOverHom B S hS hZ hV mU mW hcov hY hcomm) = mU :=
  pullback_map_glueingFullOverHom_eq B S hS hZ hV mU mW hcov hY hcomm jU mU
    (glueingFullHom_app_eq_left B S hS hZ hV mU mW hcov hY hcomm)

include hZ hV hcov hY hcomm in
/-- **The base change to `W` of the glued morphism is the second datum.** -/
theorem pullback_map_glueingFullOverHom_right :
    (Over.pullback (yoneda.map jW)).map
        (glueingFullOverHom B S hS hZ hV mU mW hcov hY hcomm) = mW :=
  pullback_map_glueingFullOverHom_eq B S hS hZ hV mU mW hcov hY hcomm jW mW
    (glueingFullHom_app_eq_right B S hS hZ hV mU mW hcov hY hcomm)

end Full

include hZ hV in
/-- **The comparison functor into the `2`-fibre product is full.** A morphism of the `2`-fibre
product is a pair of morphisms of the base changes to `U` and to `W` agreeing over `V`; the sheaf
condition at the Mayer--Vietoris square glues them to a morphism over the base, whose two base
changes are the given pair. -/
theorem full_glueingFunctor
    (hcov : Sieve.ofTwoArrows jU jW ∈ BigFppfOver.topology B S hS Z) :
    (glueingFunctor B S hS hV.w).Full where
  map_surjective {F G} m := by
    have hw : (Over.pullback (yoneda.map iU)).map
          ((ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS U)).map m.hom.left) ≫
          (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS V)).map
            ((baseChangeSquareIso B S hS hV.w).hom.app G) =
        (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS V)).map
            ((baseChangeSquareIso B S hS hV.w).hom.app F) ≫
          (Over.pullback (yoneda.map iW)).map
            ((ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS W)).map m.hom.right) :=
      (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS V)).congr_map m.hom.w
    rw [baseChangeSquareIso_hom_app_left, baseChangeSquareIso_hom_app_left,
      Over.pullbackSquareIso_hom_app, Over.pullbackSquareIso_hom_app] at hw
    refine ⟨ObjectProperty.homMk (glueingFullOverHom B S hS hZ hV
      ((ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS U)).map m.hom.left)
      ((ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS W)).map m.hom.right)
      hcov G.property.1.isSheaf hw), ?_⟩
    refine ObjectProperty.hom_ext _ (Comma.hom_ext _ _ ?_ ?_)
    · rw [glueingFunctor_map_hom_left]
      refine (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS U)).map_injective ?_
      rw [ι_map_baseChange_map]
      exact pullback_map_glueingFullOverHom_left B S hS hZ hV _ _ hcov G.property.1.isSheaf hw
    · rw [glueingFunctor_map_hom_right]
      refine (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS W)).map_injective ?_
      rw [ι_map_baseChange_map]
      exact pullback_map_glueingFullOverHom_right B S hS hZ hV _ _ hcov G.property.1.isSheaf hw

/-! ### The glueing functor out of the `2`-fibre product -/

/-- The glueing datum carried by an object of the `2`-fibre product
`FP_U ×_{FP_V} FP_W`: an identification of the base changes to `V` of its two components. -/
noncomputable def isoCommaIso (T : IsoComma (baseChange B S hS iU) (baseChange B S hS iW)) :
    (Over.pullback (yoneda.map iU)).obj T.obj.left.obj ≅
      (Over.pullback (yoneda.map iW)).obj T.obj.right.obj :=
  haveI := T.property
  (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS V)).mapIso (asIso T.obj.hom)

/-- A morphism of the `2`-fibre product commutes with the identifications over `V`. -/
theorem isoCommaIso_naturality {T T' : IsoComma (baseChange B S hS iU) (baseChange B S hS iW)}
    (m : T ⟶ T') :
    (Over.pullback (yoneda.map iU)).map
          ((ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS U)).map m.hom.left) ≫
        (isoCommaIso B S hS T').hom =
      (isoCommaIso B S hS T).hom ≫ (Over.pullback (yoneda.map iW)).map
        ((ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS W)).map m.hom.right) :=
  (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS V)).congr_map m.hom.w

/-- The presheaf glued from an object of the `2`-fibre product `FP_U ×_{FP_V} FP_W`: its sections
over `X` are the pairs of a section of the first component over `U ⨯ X` and a section of the
second over `W ⨯ X` agreeing over `V ⨯ X`. -/
noncomputable def gluedPresheafOfIsoComma
    (T : IsoComma (baseChange B S hS iU) (baseChange B S hS iW)) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  gluedPresheaf (isSubterminal_of_mono_isTerminal hZ jU)
    (isSubterminal_of_mono_isTerminal hZ jW)
    (hV.isSubterminal (isSubterminal_of_mono_isTerminal hZ jU)
      (isSubterminal_of_mono_isTerminal hZ jW))
    (isoCommaIso B S hS T)

/-- **The glueing functor from the `2`-fibre product `FP_U ×_{FP_V} FP_W` to presheaves on the
big fppf site of `S`**, taking an object to the presheaf glued from its two components. -/
noncomputable def gluedPresheafFunctor :
    IsoComma (baseChange B S hS iU) (baseChange B S hS iW) ⥤
      ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) where
  obj T := gluedPresheafOfIsoComma B S hS hZ hV T
  map {T T'} m :=
    gluedPresheafMap _ _ _ (isoCommaIso B S hS T) (isoCommaIso B S hS T')
      (isoCommaIso_naturality B S hS m)
  map_id T := by
    ext X p
    exact Subtype.ext (Prod.ext rfl rfl)
  map_comp f g := by
    ext X p
    exact Subtype.ext (Prod.ext rfl rfl)

/-! ### The glued space is an algebraic space of finite presentation over the base -/

section Cover

/-- **The presheaf glued from two algebraic spaces over an open covering of the base is an
algebraic space over `S`.** It is an fppf sheaf by
`CategoryTheory.SubterminalGlueing.isSheaf_gluedPresheaf`, and its restrictions to `U` and to `W`
are the two presheaves glued by `CategoryTheory.SubterminalGlueing.prodGluedRestrictLeftIso` and
`CategoryTheory.SubterminalGlueing.prodGluedRestrictRightIso`, so the criterion
`AlgebraicGeometry.isAlgebraicSpace_iff_isAlgebraicSpace_relocalizeRestrict_pair` applies. -/
theorem isAlgebraicSpace_gluedPresheaf
    (hUopen : IsOpenImmersion (B.inclusion.map U.hom))
    (hWopen : IsOpenImmersion (B.inclusion.map W.hom))
    (hScov : ∀ x : S, x ∈ Set.range (B.inclusion.map U.hom) ∨
      x ∈ Set.range (B.inclusion.map W.hom))
    {A : Over (yoneda.obj U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    {Bb : Over (yoneda.obj W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    (φ : (Over.pullback (yoneda.map iU)).obj A ≅ (Over.pullback (yoneda.map iW)).obj Bb)
    (hA : IsAlgebraicSpace B S hS A.left) (hBb : IsAlgebraicSpace B S hS Bb.left) :
    IsAlgebraicSpace B S hS (gluedPresheaf (isSubterminal_of_mono_isTerminal hZ jU)
      (isSubterminal_of_mono_isTerminal hZ jW)
      (hV.isSubterminal (isSubterminal_of_mono_isTerminal hZ jU)
        (isSubterminal_of_mono_isTerminal hZ jW)) φ) := by
  refine (isAlgebraicSpace_iff_isAlgebraicSpace_relocalizeRestrict_pair B S hS
    U.left.obj W.left.obj U.left.property W.left.property U.hom W.hom hUopen hWopen hScov _
    (isSheaf_gluedPresheaf _ _ _ φ (BigFppfOver.topology B S hS) hA.isSheaf hBb.isSheaf)).2
    ⟨?_, ?_⟩
  · exact (isAlgebraicSpace_restrict_iff_product B U.left.obj S U.left.property hS U.hom _).2
      (hA.of_iso (prodGluedRestrictLeftIso _ _ _ φ hZ hV).symm)
  · exact (isAlgebraicSpace_restrict_iff_product B W.left.obj S W.left.property hS W.hom _).2
      (hBb.of_iso (prodGluedRestrictRightIso _ _ _ φ hZ hV).symm)

/-- **The structure morphism of the glued presheaf is of finite presentation.** Its base changes
over the two members of the Zariski covering of the base given by `U` and `W` are the structure
morphisms of the two presheaves glued, by
`CategoryTheory.SubterminalGlueing.isPullback_gluedRestrictLeft` and
`CategoryTheory.SubterminalGlueing.isPullback_gluedRestrictRight`, so finite presentation
descends by `AlgebraicGeometry.Space.isFinitePresentation_iff_forall_zariskiCover`. -/
theorem isFinitePresentation_gluedOver
    (hjU : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map jU))
    (hjW : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map jW))
    (hsurj : ∀ x : (BigFppfOver.toScheme B S hS).obj Z,
      x ∈ Set.range ((BigFppfOver.toScheme B S hS).map jU) ∨
        x ∈ Set.range ((BigFppfOver.toScheme B S hS).map jW))
    (hUopen : IsOpenImmersion (B.inclusion.map U.hom))
    (hWopen : IsOpenImmersion (B.inclusion.map W.hom))
    (hScov : ∀ x : S, x ∈ Set.range (B.inclusion.map U.hom) ∨
      x ∈ Set.range (B.inclusion.map W.hom))
    {A : Over (yoneda.obj U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    {Bb : Over (yoneda.obj W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    (φ : (Over.pullback (yoneda.map iU)).obj A ≅ (Over.pullback (yoneda.map iW)).obj Bb)
    (hA : IsAlgebraicSpace B S hS A.left) (hBb : IsAlgebraicSpace B S hS Bb.left)
    (hAfp : Space.IsFinitePresentation B S hS A.hom)
    (hBfp : Space.IsFinitePresentation B S hS Bb.hom) :
    Space.IsFinitePresentation B S hS
      (gluedOver (isSubterminal_of_mono_isTerminal hZ jU)
        (isSubterminal_of_mono_isTerminal hZ jW)
        (hV.isSubterminal (isSubterminal_of_mono_isTerminal hZ jU)
          (isSubterminal_of_mono_isTerminal hZ jW)) φ hZ).hom := by
  have : Mono (yoneda.map jU) := NatTrans.mono_of_mono_app _
  have : Mono (yoneda.map jW) := NatTrans.mono_of_mono_app _
  refine (Space.isFinitePresentation_iff_forall_zariskiCover B S hS
    (isAlgebraicSpace_gluedPresheaf B S hS hZ hV hUopen hWopen hScov φ hA hBb)
    (isAlgebraicSpace_yoneda B S hS Z) _
    (Space.isZariskiCover_rangePair B S hS hjU hjW
      (ofTwoArrows_mem_topology B S hS jU jW hjU hjW hsurj))).2 ?_
  rintro ⟨_ | _⟩
  · rw [Space.rangePair_false]
    exact Space.isFinitePresentation_pullback_snd_range B S hS
      (isPullback_gluedRestrictRight _ _ _ φ hZ hV) hBfp
  · rw [Space.rangePair_true]
    exact Space.isFinitePresentation_pullback_snd_range B S hS
      (isPullback_gluedRestrictLeft _ _ _ φ hZ hV) hAfp

/-- **The quasi-inverse of
`AlgebraicGeometry.FinitePresentationSpacesOver.glueingFunctor`.** For an open covering of the
base by two opens `U` and `W` with intersection `V`, the glueing functor of
`AlgebraicGeometry.FinitePresentationSpacesOver.gluedPresheafFunctor` lands in the algebraic
spaces of finite presentation over the base.

The covering hypotheses are stated twice, once for the structure morphisms of `U` and `W` to the
terminal object of the site and once for their structure morphisms to `S`; at the canonical
terminal object `Over.mk (𝟙 (B.obj hS))` the two forms agree by
`AlgebraicGeometry.toScheme_map_mkIdTerminal_from`. -/
noncomputable def glueingQuasiInverse
    (hjU : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map jU))
    (hjW : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map jW))
    (hsurj : ∀ x : (BigFppfOver.toScheme B S hS).obj Z,
      x ∈ Set.range ((BigFppfOver.toScheme B S hS).map jU) ∨
        x ∈ Set.range ((BigFppfOver.toScheme B S hS).map jW))
    (hUopen : IsOpenImmersion (B.inclusion.map U.hom))
    (hWopen : IsOpenImmersion (B.inclusion.map W.hom))
    (hScov : ∀ x : S, x ∈ Set.range (B.inclusion.map U.hom) ∨
      x ∈ Set.range (B.inclusion.map W.hom)) :
    IsoComma (baseChange B S hS iU) (baseChange B S hS iW) ⥤
      FinitePresentationSpacesOver B S hS Z :=
  ObjectProperty.lift _
    (gluedPresheafFunctor B S hS hZ hV ⋙
      (Over.equivalenceOfIsTerminal (hZ.isTerminalObj yoneda Z)).inverse)
    (fun T => ⟨isAlgebraicSpace_gluedPresheaf B S hS hZ hV hUopen hWopen hScov
        (isoCommaIso B S hS T) T.obj.left.property.1 T.obj.right.property.1,
      isFinitePresentation_gluedOver B S hS hZ hV hjU hjW hsurj hUopen hWopen hScov
        (isoCommaIso B S hS T) T.obj.left.property.1 T.obj.right.property.1
        T.obj.left.property.2 T.obj.right.property.2⟩)

/-! ### The equivalence -/

variable (hjU : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map jU))
  (hjW : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map jW))
  (hsurj : ∀ x : (BigFppfOver.toScheme B S hS).obj Z,
    x ∈ Set.range ((BigFppfOver.toScheme B S hS).map jU) ∨
      x ∈ Set.range ((BigFppfOver.toScheme B S hS).map jW))
  (hUopen : IsOpenImmersion (B.inclusion.map U.hom))
  (hWopen : IsOpenImmersion (B.inclusion.map W.hom))
  (hScov : ∀ x : S, x ∈ Set.range (B.inclusion.map U.hom) ∨
    x ∈ Set.range (B.inclusion.map W.hom))

include hZ hV hjU hjW hsurj hUopen hWopen hScov in
/-- The compatibility over `V` of the two restriction comparisons of the glued space, read in the
slice of presheaves on the big fppf site. -/
theorem counitSquare (T : IsoComma (baseChange B S hS iU) (baseChange B S hS iW)) :
    (Over.pullback (yoneda.map iU)).map (gluedRestrictLeftIso
          (isSubterminal_of_mono_isTerminal hZ jU) (isSubterminal_of_mono_isTerminal hZ jW)
          (hV.isSubterminal (isSubterminal_of_mono_isTerminal hZ jU)
            (isSubterminal_of_mono_isTerminal hZ jW)) (isoCommaIso B S hS T) hZ hV).hom ≫
        (isoCommaIso B S hS T).hom =
      (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS V)).map
          ((baseChangeSquareIso B S hS hV.w).hom.app
            ((glueingQuasiInverse B S hS hZ hV hjU hjW hsurj hUopen hWopen hScov).obj T)) ≫
        (Over.pullback (yoneda.map iW)).map (gluedRestrictRightIso
          (isSubterminal_of_mono_isTerminal hZ jU) (isSubterminal_of_mono_isTerminal hZ jW)
          (hV.isSubterminal (isSubterminal_of_mono_isTerminal hZ jU)
            (isSubterminal_of_mono_isTerminal hZ jW)) (isoCommaIso B S hS T) hZ hV).hom := by
  rw [baseChangeSquareIso_hom_app_left]
  exact gluedRestrict_comm (isSubterminal_of_mono_isTerminal hZ jU)
    (isSubterminal_of_mono_isTerminal hZ jW)
    (hV.isSubterminal (isSubterminal_of_mono_isTerminal hZ jU)
      (isSubterminal_of_mono_isTerminal hZ jW)) (isoCommaIso B S hS T) hZ hV

include hZ hV hjU hjW hsurj hUopen hWopen hScov in
/-- **The two restrictions of the glued space are the two spaces glued.** This is the counit of
the equivalence of Stacks 0E8Z at a single glueing datum. -/
noncomputable def counitObjIso
    (T : IsoComma (baseChange B S hS iU) (baseChange B S hS iW)) :
    (glueingQuasiInverse B S hS hZ hV hjU hjW hsurj hUopen hWopen hScov ⋙
      glueingFunctor B S hS hV.w).obj T ≅ T :=
  ObjectProperty.isoMk _ (Comma.isoMk
    (ObjectProperty.isoMk _ (gluedRestrictLeftIso
      (isSubterminal_of_mono_isTerminal hZ jU) (isSubterminal_of_mono_isTerminal hZ jW)
      (hV.isSubterminal (isSubterminal_of_mono_isTerminal hZ jU)
        (isSubterminal_of_mono_isTerminal hZ jW)) (isoCommaIso B S hS T) hZ hV))
    (ObjectProperty.isoMk _ (gluedRestrictRightIso
      (isSubterminal_of_mono_isTerminal hZ jU) (isSubterminal_of_mono_isTerminal hZ jW)
      (hV.isSubterminal (isSubterminal_of_mono_isTerminal hZ jU)
        (isSubterminal_of_mono_isTerminal hZ jW)) (isoCommaIso B S hS T) hZ hV))
    (ObjectProperty.hom_ext _
      (counitSquare B S hS hZ hV hjU hjW hsurj hUopen hWopen hScov T)))

include hZ hV hjU hjW hsurj hUopen hWopen hScov in
/-- **The counit of the equivalence of Stacks 0E8Z**: glueing two algebraic spaces of finite
presentation along the intersection of the two opens and restricting back recovers the glueing
datum. -/
noncomputable def counitIso :
    glueingQuasiInverse B S hS hZ hV hjU hjW hsurj hUopen hWopen hScov ⋙
        glueingFunctor B S hS hV.w ≅
      𝟭 (IsoComma (baseChange B S hS iU) (baseChange B S hS iW)) :=
  NatIso.ofComponents (counitObjIso B S hS hZ hV hjU hjW hsurj hUopen hWopen hScov)
    fun {T T'} m => ObjectProperty.hom_ext _ (Comma.hom_ext _ _
      ((ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS U)).map_injective
        (gluedRestrictLeftIso_naturality (isSubterminal_of_mono_isTerminal hZ jU)
          (isSubterminal_of_mono_isTerminal hZ jW)
          (hV.isSubterminal (isSubterminal_of_mono_isTerminal hZ jU)
            (isSubterminal_of_mono_isTerminal hZ jW)) (isoCommaIso B S hS T)
          (isoCommaIso B S hS T') hZ hV (isoCommaIso_naturality B S hS m)))
      ((ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS W)).map_injective
        (gluedRestrictRightIso_naturality (isSubterminal_of_mono_isTerminal hZ jU)
          (isSubterminal_of_mono_isTerminal hZ jW)
          (hV.isSubterminal (isSubterminal_of_mono_isTerminal hZ jU)
            (isSubterminal_of_mono_isTerminal hZ jW)) (isoCommaIso B S hS T)
          (isoCommaIso B S hS T') hZ hV (isoCommaIso_naturality B S hS m))))

include hZ hV hjU hjW hsurj hUopen hWopen hScov in
/-- **The comparison functor into the `2`-fibre product is essentially surjective**: every
glueing datum is, up to isomorphism, the datum of restrictions of the space glued from it. -/
theorem essSurj_glueingFunctor : (glueingFunctor B S hS hV.w).EssSurj where
  mem_essImage T :=
    ⟨(glueingQuasiInverse B S hS hZ hV hjU hjW hsurj hUopen hWopen hScov).obj T,
      ⟨(counitIso B S hS hZ hV hjU hjW hsurj hUopen hWopen hScov).app T⟩⟩

include hZ hV hjU hjW hsurj hUopen hWopen hScov in
/-- **The unit of the equivalence of Stacks 0E8Z**: an algebraic space of finite presentation
over the base is glued from its two restrictions. It is the comparison deduced from the counit by
cancelling the fully faithful comparison functor. -/
noncomputable def unitIso :
    𝟭 (FinitePresentationSpacesOver B S hS Z) ≅
      glueingFunctor B S hS hV.w ⋙
        glueingQuasiInverse B S hS hZ hV hjU hjW hsurj hUopen hWopen hScov :=
  have := full_glueingFunctor B S hS hZ hV
    (ofTwoArrows_mem_topology B S hS jU jW hjU hjW hsurj)
  have := faithful_glueingFunctor B S hS hZ hV
    (ofTwoArrows_mem_topology B S hS jU jW hjU hjW hsurj)
  Functor.fullyFaithfulCancelRight (glueingFunctor B S hS hV.w)
    (Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm ≪≫
      Functor.isoWhiskerLeft _
        (counitIso B S hS hZ hV hjU hjW hsurj hUopen hWopen hScov).symm ≪≫
      (Functor.associator _ _ _).symm)

end Cover

end FinitePresentationSpacesOver

end AlgebraicGeometry

end
