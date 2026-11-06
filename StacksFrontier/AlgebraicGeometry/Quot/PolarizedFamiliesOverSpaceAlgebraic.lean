module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesOverSpace
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedStackUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalenceUniverses
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsSection
public import StacksFrontier.CategoryTheory.FiberedCategory.SliceAsElements
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality

/-!
# Polarized proper schemes over an algebraic space form an algebraic stack, given the absolute case

The second sentence of **Stacks 0D4X** says that for every algebraic space `A` the stack
`A-Polarized` of Remark 0D1N is algebraic, and its proof is: `A-Polarized` is the 2-fibre product
of `𝒫olarized` with `(Sch/A)` over the big fppf site (Stacks 0D1N), and algebraic stacks have
2-fibre products (Stacks 04T2). This file carries out that argument, with the algebraicity of
`𝒫olarized` as its one input.

Over a terminal base `S` of the site:

* the category `AlgebraicGeometry.PolarizedFamilyOver` of polarized families over `A`, with the
  projection `AlgebraicGeometry.PolarizedFamilyOver.projection` to the big fppf site of `S`, is
  fibred in groupoids;
* it is equivalent over the site to the 2-fibre product, over the stack of the terminal object of
  the site (an algebraic stack, Stacks 04X5), of `𝒫olarized` with the stack `𝒮_A` of `A` (an
  algebraic stack, Stacks 026O), which is an algebraic stack by Stacks 04T2.

## Main results

* `AlgebraicGeometry.PolarizedFamilyOver.projection_isFiberedInGroupoids`: polarized families over
  `A` form a category fibred in groupoids over the big fppf site of `S`.
* `AlgebraicGeometry.PolarizedFamilyOver.isAlgebraicStack_of_isAlgebraicStack`: if `𝒫olarized`
  is an algebraic stack, so is `A-Polarized` for every algebraic space `A`.

## Implementation notes

The theorem takes the algebraicity of `𝒫olarized` as its hypothesis.

## References

* [Stacks Project, Tag 0D4X](https://stacks.math.columbia.edu/tag/0D4X)
* [Stacks Project, Tag 0D1N](https://stacks.math.columbia.edu/tag/0D1N)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.PolarizedFamilyOver

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

variable (B S hS A) in
/-- **Remark 0D1N, the projection.** A polarized family over `A` lies over its base scheme, read
as a scheme over the base of the site through its structure morphism. -/
def projection : PolarizedFamilyOver B S hS A ⥤ BigFppfOver B S hS where
  obj X := Over.mk X.toBase
  map f := Hom.over f
  map_id _ := Over.OverMorphism.ext rfl
  map_comp _ _ := Over.OverMorphism.ext rfl

/-- The projection sends a polarized family over `A` to its structure morphism. -/
@[simp]
theorem projection_obj (X : PolarizedFamilyOver B S hS A) :
    (projection B S hS A).obj X = Over.mk X.toBase := rfl

/-- The projection sends a morphism of polarized families over `A` to its base map. -/
@[simp]
theorem projection_map_left {X Y : PolarizedFamilyOver B S hS A} (f : X ⟶ Y) :
    ((projection B S hS A).map f).left = PolarizedFamily.Hom.baseMap f.polarizedHom := rfl

/-- The base change of a polarized family over `A` along a morphism into its base scheme which
lifts a given morphism of polarized families: the source family, with the composite structure
morphism and the pulled back point. -/
def ofLift (X : PolarizedFamilyOver B S hS A) {y : PolarizedFamily B} (φ : y ⟶ X.polarized) :
    PolarizedFamilyOver B S hS A where
  polarized := y
  toBase := PolarizedFamily.Hom.baseMap φ ≫ X.toBase
  point := A.map (Quiver.Hom.op (Over.homMk (PolarizedFamily.Hom.baseMap φ) rfl :
    Over.mk (PolarizedFamily.Hom.baseMap φ ≫ X.toBase) ⟶ Over.mk X.toBase)) X.point

/-- The morphism of polarized families over `A` from a base change to the family it is a base
change of. -/
def ofLiftHom (X : PolarizedFamilyOver B S hS A) {y : PolarizedFamily B}
    (φ : y ⟶ X.polarized) : ofLift X φ ⟶ X where
  polarizedHom := φ
  base_comm := rfl
  point_comm := rfl

/-- **Polarized families over `A` form a category fibred in groupoids** over the big fppf site of
`S`: a morphism of base schemes lifts by base change of the polarized family and pullback of the
point, and fill-ins are those of the polarized families, the compatibility with the points being
automatic. -/
theorem projection_isFiberedInGroupoids : (projection B S hS A).IsFiberedInGroupoids where
  exists_lift {V U} f X hX := by
    subst hX
    obtain ⟨Vl, ⟨⟩, Vh⟩ := V
    have hp := (polarizedProjection_isFiberedInGroupoids_unconditional (B := B))
    obtain ⟨y, φ, hφ⟩ := hp.exists_lift f.left X.polarized rfl
    have hyb : y.base = Vl := IsHomLift.domain_eq (polarizedProjection B) f.left φ
    subst hyb
    have hφb : PolarizedFamily.Hom.baseMap φ = f.left := by
      have hfac := IsHomLift.fac' (polarizedProjection B) f.left φ
      change PolarizedFamily.Hom.baseMap φ = _ at hfac
      rw [hfac]
      show 𝟙 _ ≫ f.left ≫ 𝟙 _ = f.left
      simp
    have hV : PolarizedFamily.Hom.baseMap φ ≫ X.toBase = Vh := by
      rw [hφb]
      exact Over.w f
    refine ⟨ofLift X φ, ofLiftHom X φ, IsHomLift.of_fac' _ f _ ?_ rfl ?_⟩
    · show Over.mk (PolarizedFamily.Hom.baseMap φ ≫ X.toBase) = Over.mk Vh
      rw [hV]
    · apply Over.OverMorphism.ext
      simp only [Over.comp_left, Over.eqToHom_left, eqToHom_refl, Category.comp_id,
        projection_map_left]
      show PolarizedFamily.Hom.baseMap φ = _
      refine hφb.trans ?_
      show f.left = 𝟙 _ ≫ f.left
      exact (Category.id_comp _).symm
  unique_lift {X Y Z} φ ψ f hcomm := by
    have hp := (polarizedProjection_isFiberedInGroupoids_unconditional (B := B))
    have hcomm' : f.left ≫ (polarizedProjection B).map φ.polarizedHom =
        (polarizedProjection B).map ψ.polarizedHom :=
      congrArg CommaMorphism.left hcomm
    obtain ⟨χ, ⟨hχ₁, hχ₂⟩, huniq⟩ := hp.unique_lift φ.polarizedHom ψ.polarizedHom f.left hcomm'
    have hχb : PolarizedFamily.Hom.baseMap χ = f.left := hχ₁
    have hbase : PolarizedFamily.Hom.baseMap χ ≫ Y.toBase = Z.toBase := by
      rw [hχb]
      exact Over.w f
    have hover : (Over.homMk (PolarizedFamily.Hom.baseMap χ) hbase :
        Over.mk Z.toBase ⟶ Over.mk Y.toBase) ≫ Hom.over φ = Hom.over ψ := by
      apply Over.OverMorphism.ext
      show PolarizedFamily.Hom.baseMap χ ≫ PolarizedFamily.Hom.baseMap φ.polarizedHom =
        PolarizedFamily.Hom.baseMap ψ.polarizedHom
      rw [← PolarizedFamily.comp_baseMap, hχ₂]
    let χ' : Z ⟶ Y :=
      { polarizedHom := χ
        base_comm := hbase
        point_comm := by
          have hφ : A.map (Quiver.Hom.op (Hom.over φ)) X.point = Y.point := φ.point_comm
          have hψ : A.map (Quiver.Hom.op (Hom.over ψ)) X.point = Z.point := ψ.point_comm
          rw [← hφ, ← hψ, ← hover, op_comp, Functor.map_comp]
          rfl }
    refine ⟨χ', ⟨Over.OverMorphism.ext hχb, Hom.ext hχ₂⟩, ?_⟩
    rintro χ'' ⟨h₁, h₂⟩
    exact Hom.ext (huniq χ''.polarizedHom ⟨congrArg CommaMorphism.left h₁,
      congrArg Hom.polarizedHom h₂⟩)

/-! ### The 2-fibre product with the stack of the algebraic space -/

section TwoFibreProduct

variable (hT : IsTerminal (B.obj hS))

variable (B S hS) in
/-- The terminal object of the big fppf site of `S`. -/
abbrev terminalObj : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))

variable (B S hS) in
/-- The stack of the terminal object of the big fppf site of `S`. -/
abbrev terminalStack : BasedCategory (BigFppfOver B S hS) :=
  BasedCategory.ofFunctor (Over.forget (terminalObj B S hS))

variable (B S hS) in
/-- The functor from the big fppf site of `S` to its slice over the terminal object. -/
abbrev toTerminalSlice : BigFppfOver B S hS ⥤ Over (terminalObj B S hS) :=
  (Over.equivalenceOfIsTerminal Over.mkIdTerminal).inverse

/-- The 1-morphism from a category over the big fppf site of `S` to the stack of the terminal
object. -/
def toTerminalStack (𝒳 : BasedCategory.{u, u + 1} (BigFppfOver B S hS)) :
    𝒳 ⥤ᵇ terminalStack B S hS where
  toFunctor := 𝒳.p ⋙ toTerminalSlice B S hS
  w := rfl

variable (B hS) in
/-- `𝒫olarized` over the big fppf site of the terminal base `S`, as a category over that site. -/
abbrev polarizedBased : BasedCategory (BigFppfOver B S hS) :=
  BasedCategory.ofFunctor (polarizedSliceProjection B hS hT)

variable (B hS A) in
/-- The stack `𝒮_A` of the presheaf `A`, as a category over the big fppf site of `S`. -/
abbrev spaceBased : BasedCategory (BigFppfOver B S hS) :=
  presheafOfGroupoids (A ⋙ typeToGrpd)

variable (B hS A) in
/-- The objects of the stack `𝒮_A`: the elements of `A`. -/
abbrev SpaceObj :=
  Pseudofunctor.CoGrothendieck ((A ⋙ typeToGrpd) ⋙ Grpd.forgetToCat).toPseudofunctor'

variable (B hS A) in
/-- The structure functor of the stack `𝒮_A`. -/
abbrev spaceForget : SpaceObj B hS A ⥤ BigFppfOver B S hS :=
  Pseudofunctor.CoGrothendieck.forget _

/-- The polarized family underlying a polarized family over `A` lies over its base scheme, read in
the slice over the terminal base. -/
theorem sliceProjection_obj_polarized (X : PolarizedFamilyOver B S hS A) :
    (polarizedSliceProjection B hS hT).obj X.polarized = Over.mk X.toBase :=
  Functor.sliceAtTerminal_obj_eq _ hT rfl

/-- The base map of a morphism of polarized families, read in the slice over the terminal base, is
its base map. -/
theorem forget_map_sliceProjection_map {x y : PolarizedFamily B} (φ : x ⟶ y) :
    (Over.forget (B.obj hS)).map ((polarizedSliceProjection B hS hT).map φ) =
      PolarizedFamily.Hom.baseMap φ := rfl

/-- A morphism of the polarized families of two polarized families over `A`, compatible with the
structure morphisms, read in the slice over the terminal base, is the morphism of schemes over the
base of the site it induces. -/
theorem sliceProjection_map_comp_eqToHom' {X Y : PolarizedFamilyOver B S hS A}
    (φ : X.polarized ⟶ Y.polarized) (hφ : PolarizedFamily.Hom.baseMap φ ≫ Y.toBase = X.toBase) :
    (polarizedSliceProjection B hS hT).map φ ≫ eqToHom (sliceProjection_obj_polarized hT Y) =
      eqToHom (sliceProjection_obj_polarized hT X) ≫
        (Over.homMk (PolarizedFamily.Hom.baseMap φ) hφ : Over.mk X.toBase ⟶ Over.mk Y.toBase) := by
  apply (Over.forget (B.obj hS)).map_injective
  simp only [Functor.map_comp, eqToHom_map]
  rw [forget_map_sliceProjection_map]
  show _ ≫ 𝟙 _ = 𝟙 _ ≫ _
  exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- The base map of a morphism of polarized families over `A`, read in the slice over the terminal
base, is its morphism of schemes over the base of the site. -/
theorem sliceProjection_map_comp_eqToHom {X Y : PolarizedFamilyOver B S hS A} (f : X ⟶ Y) :
    (polarizedSliceProjection B hS hT).map f.polarizedHom ≫
        eqToHom (sliceProjection_obj_polarized hT Y) =
      eqToHom (sliceProjection_obj_polarized hT X) ≫ Hom.over f :=
  sliceProjection_map_comp_eqToHom' hT f.polarizedHom f.base_comm

/-- The point of `A` carried by a polarized family over `A`, as an object of the stack `𝒮_A`,
over the base scheme of its polarized family read in the slice over the terminal base. -/
def toElement (X : PolarizedFamilyOver B S hS A) : (SpaceObj B hS A) :=
  ⟨(polarizedSliceProjection B hS hT).obj X.polarized,
    Discrete.mk (A.map (eqToHom (sliceProjection_obj_polarized hT X)).op X.point)⟩

/-- The morphism of `𝒮_A` underlying a morphism of polarized families over `A`. -/
def toElementHom {X Y : PolarizedFamilyOver B S hS A} (f : X ⟶ Y) :
    toElement hT X ⟶ toElement hT Y :=
  ⟨(polarizedSliceProjection B hS hT).map f.polarizedHom, Discrete.eqToHom (by
    change A.map (eqToHom (sliceProjection_obj_polarized hT X)).op X.point =
      A.map ((polarizedSliceProjection B hS hT).map f.polarizedHom).op
        (A.map (eqToHom (sliceProjection_obj_polarized hT Y)).op Y.point)
    rw [← Functor.map_comp_apply, ← op_comp, sliceProjection_map_comp_eqToHom, op_comp,
      Functor.map_comp_apply]
    exact congrArg _ f.point_comm.symm)⟩

variable (B hS A) in
/-- The 2-fibre product, over the stack of the terminal object of the site, of `𝒫olarized` with
the stack `𝒮_A` of the presheaf `A`. -/
abbrev TwoFibreProductPt :=
  TwoFibreProductOver (polarizedSliceProjection B hS hT) (spaceForget B hS A)
    (Over.forget (terminalObj B S hS))
    (polarizedSliceProjection B hS hT ⋙ toTerminalSlice B S hS)
    ((spaceForget B hS A) ⋙ toTerminalSlice B S hS)

/-- The object of the 2-fibre product attached to a polarized family over `A`: its polarized
family and its point of `A`, with the identity comparison over the terminal object. -/
abbrev toTwoFibreProductObj (X : PolarizedFamilyOver B S hS A) : TwoFibreProductPt B hS A hT where
  base := (polarizedSliceProjection B hS hT).obj X.polarized
  x := X.polarized
  y := toElement hT X
  hx := rfl
  hy := rfl
  iso := Iso.refl _
  vertical := IsHomLift.id rfl

/-- The morphism of the 2-fibre product attached to a morphism of polarized families over
`A`. -/
def toTwoFibreProductMap {X Y : PolarizedFamilyOver B S hS A} (f : X ⟶ Y) :
    toTwoFibreProductObj hT X ⟶ toTwoFibreProductObj hT Y :=
  TwoFibreProductOver.Hom.mk' f.polarizedHom (toElementHom hT f)
    (by simp only [eqToHom_refl, Category.id_comp, Category.comp_id]; rfl)
    (by simp only [Iso.refl_hom]; rfl)

/-- The morphism of polarized families of `toTwoFibreProductMap f` is that of `f`. -/
theorem toTwoFibreProductMap_a {X Y : PolarizedFamilyOver B S hS A} (f : X ⟶ Y) :
    (toTwoFibreProductMap hT f).a = f.polarizedHom := rfl

/-- The morphism of elements of `A` of `toTwoFibreProductMap f` is `toElementHom f`. -/
theorem toTwoFibreProductMap_b {X Y : PolarizedFamilyOver B S hS A} (f : X ⟶ Y) :
    (toTwoFibreProductMap hT f).b = toElementHom hT f := rfl

/-- **The comparison functor of Remark 0D1N over a terminal base**: a polarized family over `A`
is sent to its polarized family and its point of `A`, with the identity comparison over the
terminal object. -/
abbrev toTwoFibreProduct : PolarizedFamilyOver B S hS A ⥤ TwoFibreProductPt B hS A hT where
  obj X := toTwoFibreProductObj hT X
  map f := toTwoFibreProductMap hT f
  map_id X := by
    refine TwoFibreProductOver.Hom.ext' ?_ (PresheafOfCategories.elements_hom_ext (G := A) _ _ ?_)
    · rw [toTwoFibreProductMap_a, TwoFibreProductOver.id_a]
      rfl
    · rw [toTwoFibreProductMap_b, TwoFibreProductOver.id_b]
      exact (polarizedSliceProjection B hS hT).map_id X.polarized
  map_comp {X Y Z} f g := by
    refine TwoFibreProductOver.Hom.ext' ?_ (PresheafOfCategories.elements_hom_ext (G := A) _ _ ?_)
    · rw [TwoFibreProductOver.comp_a, toTwoFibreProductMap_a, toTwoFibreProductMap_a,
        toTwoFibreProductMap_a]
      exact comp_polarizedHom f g
    · rw [TwoFibreProductOver.comp_b, toTwoFibreProductMap_b, toTwoFibreProductMap_b,
        toTwoFibreProductMap_b]
      exact (polarizedSliceProjection B hS hT).map_comp f.polarizedHom g.polarizedHom

/-- Over a terminal base the comparison functor lies over the big fppf site: its composite with
the projection of the 2-fibre product is the projection of the polarized families over `A`. -/
theorem toTwoFibreProduct_comp_structureFunctor :
    toTwoFibreProduct hT ⋙ TwoFibreProductOver.structureFunctor _ _ _ _ _ =
      projection B S hS A := by
  refine CategoryTheory.Functor.ext (fun X => sliceProjection_obj_polarized hT X)
    (fun {X Y} f => ?_)
  show eqToHom rfl ≫ (polarizedSliceProjection B hS hT).map f.polarizedHom ≫ eqToHom rfl = _
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
  exact (show (polarizedSliceProjection B hS hT).map f.polarizedHom =
      eqToHom (sliceProjection_obj_polarized hT X) ≫ Hom.over f ≫
        eqToHom (sliceProjection_obj_polarized hT Y).symm by
    rw [← Category.assoc, ← sliceProjection_map_comp_eqToHom, Category.assoc, eqToHom_trans,
      eqToHom_refl, Category.comp_id])

/-- The comparison functor is faithful: a morphism of polarized families over `A` is determined
by its morphism of polarized families. -/
instance : (toTwoFibreProduct (A := A) hT).Faithful where
  map_injective h :=
    Hom.ext (congrArg TwoFibreProductOver.Hom.a h)

/-- In the 2-fibre product, the base map of the morphism of polarized families of a morphism
between two objects coming from polarized families over `A` is that of its morphism of elements of
`A`. -/
theorem sliceProjection_map_a_eq_base {X Y : PolarizedFamilyOver B S hS A}
    (h : (toTwoFibreProduct hT).obj X ⟶ (toTwoFibreProduct hT).obj Y) :
    (polarizedSliceProjection B hS hT).map h.a = h.b.base := by
  have ha := h.ha
  have hb := h.hb
  have e₁ := IsHomLift.fac' (polarizedSliceProjection B hS hT) h.hbase h.a
  have e₂ := IsHomLift.fac' (spaceForget B hS A) h.hbase h.b
  rw [e₁]
  show _ = (spaceForget B hS A).map h.b
  rw [e₂]
  rfl

omit hT in
/-- Cancelling an `eqToHom` against its inverse at the end of a composite. -/
theorem eqToHom_comp_assoc_eqToHom {P Q R R' : BigFppfOver B S hS} (a : P ⟶ Q) (b : Q ⟶ R)
    (h₁ : R = R') (h₂ : R' = R) : (a ≫ b ≫ eqToHom h₁) ≫ eqToHom h₂ = a ≫ b := by
  simp

/-- The comparison functor is full. -/
instance : (toTwoFibreProduct (A := A) hT).Full where
  map_surjective {X Y} h := by
    have hφ : PolarizedFamily.Hom.baseMap h.a ≫ Y.toBase = X.toBase := hT.hom_ext _ _
    have key := sliceProjection_map_comp_eqToHom' hT h.a hφ
    have hbase : h.b.base = eqToHom (sliceProjection_obj_polarized hT X) ≫
        (Over.homMk (PolarizedFamily.Hom.baseMap h.a) hφ : Over.mk X.toBase ⟶ Over.mk Y.toBase) ≫
          eqToHom (sliceProjection_obj_polarized hT Y).symm :=
      (sliceProjection_map_a_eq_base hT h).symm.trans (by
        rw [← Category.assoc, ← key, Category.assoc, eqToHom_trans, eqToHom_refl,
          Category.comp_id])
    have hfib : A.map (eqToHom (sliceProjection_obj_polarized hT X)).op X.point =
        A.map h.b.base.op (A.map (eqToHom (sliceProjection_obj_polarized hT Y)).op Y.point) :=
      Discrete.eq_of_hom h.b.fiber
    have hpt : A.map (eqToHom (sliceProjection_obj_polarized hT X)).op X.point =
        A.map (eqToHom (sliceProjection_obj_polarized hT X)).op
          (A.map (Over.homMk (PolarizedFamily.Hom.baseMap h.a) hφ :
            Over.mk X.toBase ⟶ Over.mk Y.toBase).op Y.point) := by
      refine hfib.trans ?_
      refine (A.map_comp_apply _ _ _).symm.trans
        (Eq.trans ?_ (A.map_comp_apply _ _ _))
      change A.map ((h.b.base ≫ eqToHom (sliceProjection_obj_polarized hT Y)).op) Y.point =
        A.map ((eqToHom (sliceProjection_obj_polarized hT X) ≫
          (Over.homMk (PolarizedFamily.Hom.baseMap h.a) hφ :
            Over.mk X.toBase ⟶ Over.mk Y.toBase)).op) Y.point
      have hm : h.b.base ≫ eqToHom (sliceProjection_obj_polarized hT Y) =
          eqToHom (sliceProjection_obj_polarized hT X) ≫
            (Over.homMk (PolarizedFamily.Hom.baseMap h.a) hφ :
              Over.mk X.toBase ⟶ Over.mk Y.toBase) := by
        rw [hbase]
        exact (eqToHom_comp_assoc_eqToHom _ _ _ _)
      rw [hm]
      rfl
    let u : X ⟶ Y :=
      { polarizedHom := h.a
        base_comm := hφ
        point_comm :=
          ((A.mapIso (eqToIso (sliceProjection_obj_polarized hT X)).op).toEquiv.injective
            hpt).symm }
    exact ⟨u, TwoFibreProductOver.Hom.ext' rfl
      (PresheafOfCategories.elements_hom_ext (G := A) _ _ (sliceProjection_map_a_eq_base hT h))⟩

/-- The base of the polarized family of an object of the 2-fibre product, read in the slice over
the terminal base, is the base of its element of `A`. -/
theorem ofTwoFibreProduct_base_eq (P : TwoFibreProductPt B hS A hT) :
    (polarizedSliceProjection B hS hT).obj P.x = P.y.base :=
  P.hx.trans P.hy.symm

/-- The unique morphism from the base scheme of the polarized family of an object of the 2-fibre
product to the terminal base is the base of its element of `A`. -/
theorem ofTwoFibreProduct_base_eq' (P : TwoFibreProductPt B hS A hT) :
    Over.mk (hT.from P.x.base) = P.y.base :=
  (show Over.mk (hT.from P.x.base) = (polarizedSliceProjection B hS hT).obj P.x from rfl).trans
    (ofTwoFibreProduct_base_eq hT P)

/-- The polarized family over `A` underlying an object of the 2-fibre product: its polarized
family, the unique structure morphism to the terminal base, and its point of `A` transported to
the base scheme of the polarized family. -/
abbrev ofTwoFibreProduct (P : TwoFibreProductPt B hS A hT) : PolarizedFamilyOver B S hS A where
  polarized := P.x
  toBase := hT.from P.x.base
  point := A.map (eqToHom (ofTwoFibreProduct_base_eq' hT P)).op P.y.fiber.as

/-- The isomorphism of elements of `A` from the point of `ofTwoFibreProduct P` to that of `P`. -/
def ofTwoFibreProductElementIso (P : TwoFibreProductPt B hS A hT) :
    toElement hT (ofTwoFibreProduct hT P) ≅ P.y :=
  PresheafOfCategories.elementsIsoOfBaseIso (G := A) (eqToIso (ofTwoFibreProduct_base_eq hT P))
    (by
      change A.map (eqToHom (sliceProjection_obj_polarized hT (ofTwoFibreProduct hT P))).op
          (A.map (eqToHom (ofTwoFibreProduct_base_eq' hT P)).op P.y.fiber.as) =
        A.map (eqToHom (ofTwoFibreProduct_base_eq hT P)).op P.y.fiber.as
      rw [← Functor.map_comp_apply, ← op_comp, eqToHom_trans])

/-- The base of the isomorphism `ofTwoFibreProductElementIso P` is the canonical `eqToHom`. -/
theorem ofTwoFibreProductElementIso_hom_base (P : TwoFibreProductPt B hS A hT) :
    (ofTwoFibreProductElementIso hT P).hom.base = eqToHom (ofTwoFibreProduct_base_eq hT P) :=
  rfl

/-- The comparison isomorphism from the image of `ofTwoFibreProduct P` to `P`. -/
def ofTwoFibreProductHom (P : TwoFibreProductPt B hS A hT) :
    (toTwoFibreProduct hT).obj (ofTwoFibreProduct hT P) ⟶ P where
  hbase := eqToHom P.hx
  a := 𝟙 P.x
  b := (ofTwoFibreProductElementIso hT P).hom
  ha := IsHomLift.id_lift_eqToHom_domain P.hx rfl
  hb := by
    refine IsHomLift.of_fac' _ _ _ rfl P.hy ?_
    change eqToHom (ofTwoFibreProduct_base_eq hT P) = _
    simp only [eqToHom_trans]
    rfl
  w := by
    apply (Over.forget (terminalObj B S hS)).map_injective
    have hv := P.vertical
    simp only [CategoryTheory.Functor.map_comp]
    rw [IsHomLift.fac' (Over.forget (terminalObj B S hS)) (𝟙 P.base) P.iso.hom]
    change 𝟙 _ ≫ eqToHom P.hx ≫ 𝟙 P.base ≫ eqToHom P.hy.symm =
      𝟙 _ ≫ eqToHom (ofTwoFibreProduct_base_eq hT P)
    simp only [Category.id_comp, eqToHom_trans]
    rfl

/-- The comparison morphism `ofTwoFibreProductHom P` is an isomorphism. -/
instance (P : TwoFibreProductPt B hS A hT) : IsIso (ofTwoFibreProductHom hT P) := by
  have : IsIso (ofTwoFibreProductHom hT P).b := by
    change IsIso (ofTwoFibreProductElementIso hT P).hom
    infer_instance
  have : IsIso (ofTwoFibreProductHom hT P).a := by
    change IsIso (𝟙 P.x)
    infer_instance
  have : IsIso (ofTwoFibreProductHom hT P).hbase := by
    change IsIso (eqToHom P.hx)
    infer_instance
  exact TwoFibreProductOver.isIso_of_components _

/-- The comparison functor is essentially surjective. -/
instance : (toTwoFibreProduct (A := A) hT).EssSurj where
  mem_essImage P := ⟨ofTwoFibreProduct hT P, ⟨asIso (ofTwoFibreProductHom hT P)⟩⟩

/-- The comparison functor is an equivalence. -/
instance : (toTwoFibreProduct (A := A) hT).IsEquivalence where

universe w in
/-- **The relative clause of Stacks 0D4X, given the absolute one.** Over a terminal base `S` of
the site, if `𝒫olarized` is an algebraic stack, then for every algebraic space `A` over `S` the
category `A-Polarized` of Remark 0D1N, of polarized proper schemes `(X ⟶ T, ℒ)` together with a
morphism `T ⟶ A`, is an algebraic stack.

`A-Polarized` is equivalent over the site to the 2-fibre product of `𝒫olarized` with the stack
`𝒮_A` (Remark 0D1N), over the stack of the terminal object (an algebraic stack, Stacks 04X5), and
algebraic stacks have 2-fibre products (Stacks 04TF). -/
theorem isAlgebraicStack_of_isAlgebraicStack (hA : IsAlgebraicSpace B S hS A)
    (h : Stack.IsAlgebraicStack.{u, w} B S hS (polarizedStackUnconditional B hS hT).val) :
    Stack.IsAlgebraicStack.{u, w} B S hS (BasedCategory.ofFunctor (projection B S hS A)) := by
  obtain ⟨_h𝒵fib, h𝒵st, h𝒵diag, -⟩ :=
    Stack.isAlgebraicStack_schemeFibredCategory.{u, w} B S hS (terminalObj B S hS)
  have happ := Stack.isAlgebraicStack_twoFibreProduct.{u, w} B S hS (polarizedBased B hS hT)
    (spaceBased B hS A) (terminalStack B S hS) (toTerminalStack _) (toTerminalStack _) h𝒵st
    h𝒵diag h (Stack.isAlgebraicStack_fibredCategory.{u, w} B S hS A hA)
  have h₂ : (TwoFibreProductOver.structureFunctor (polarizedSliceProjection B hS hT)
      (spaceForget B hS A) (Over.forget (terminalObj B S hS))
      (polarizedSliceProjection B hS hT ⋙ toTerminalSlice B S hS)
      (spaceForget B hS A ⋙ toTerminalSlice B S hS)).IsFiberedInGroupoids := happ.1
  have h₁ : (toTwoFibreProduct (A := A) hT ⋙ TwoFibreProductOver.structureFunctor _ _ _ _ _
      ).IsFiberedInGroupoids := by
    rw [toTwoFibreProduct_comp_structureFunctor]
    exact projection_isFiberedInGroupoids
  obtain ⟨e⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence h₁ h₂
    (toTwoFibreProduct (A := A) hT) rfl inferInstance
  exact Stack.isAlgebraicStack_of_equivalenceOver B S hS
    (StacksRepresentableCFG.EquivalenceOver.ofEq (toTwoFibreProduct_comp_structureFunctor hT)
      e).symm happ

end TwoFibreProduct

end AlgebraicGeometry.PolarizedFamilyOver

end
