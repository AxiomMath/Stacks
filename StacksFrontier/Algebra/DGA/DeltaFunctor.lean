module

public import StacksFrontier.Algebra.DGA.DerivedCategory
public import StacksFrontier.Algebra.DGA.ConeTriangle
public import StacksFrontier.Algebra.DGA.Pretriangulated
public import StacksFrontier.Algebra.DifferentialGraded.Module.LongExactSequence
public import StacksFrontier.CategoryTheory.Triangulated.Functor
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import StacksCore.Tactic.StacksAttribute

/-!
# The canonical delta-functor to the derived category of a differential graded algebra

For a differential graded algebra `A`, the canonical functor from right differential graded
`A`-modules to their derived category carries a `δ`-functor structure.  For a short exact
sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` the connecting morphism is the third arrow of the cone triangle
of `X₁ ⟶ X₂`, read in the derived category after inverting the cone-to-quotient map
`C(f) ⟶ X₃`, which is a quasi-isomorphism.

## Main results

* `Stacks.DifferentialGradedModule.DeltaFunctor.exists_deltaFunctorStructure_δ_eq`: the canonical
  functor admits a `δ`-functor
  structure whose connecting morphisms are given by that formula, together with the
  characterisation of the cone-to-quotient map by its formula on the cone's coordinates.

## Implementation notes

The canonical functor is the composite of the homotopy quotient
`DifferentialGradedModule.toHomotopyCategory` with the localization at the quasi-isomorphisms of
Tag 09KW, so its target is the derived category of Tag 09KX by definition.

The cone-to-quotient map `C(f) ⟶ X₃` sends a cone element to the image under `X₂ ⟶ X₃` of its
first coordinate.  That it is a quasi-isomorphism is read off the corresponding statement for
cochain complexes: the underlying cochain complex of the cone is the mapping cone of the
underlying map, by `coneForgetIso` below, and under that identification the cone-to-quotient map
becomes Mathlib's `CochainComplex.mappingCone.descShortComplex`, whose quasi-isomorphy for a
short exact sequence is `CochainComplex.mappingCone.quasiIso_descShortComplex`.

The sign convention is the library's.  The differential graded theory carries two triangles on a
mapping cone, differing by a sign in the third arrow — see `StacksFrontier.Algebra.DGA.ConeTriangle`
— and the `Pretriangulated` instance on the homotopy category that this library ships,
`DifferentialGradedModule.instPretriangulatedHomotopyCategory`, declares the unsigned family
`DifferentialGradedModule.coneTriangle` distinguished.  The connecting morphism is therefore
stated against `DifferentialGradedModule.coneTriangle`; against the signed family
`DifferentialGradedModule.mappingConeTriangle` the formula would acquire a minus sign and the
triangle it produces would not be the distinguished one.

## References

* [Stacks Project, Tag 09L0](https://stacks.math.columbia.edu/tag/09L0)
-/

@[expose] public section

open CategoryTheory DifferentialGradedModule

universe u v w

/- `DifferentialGradedModule.cone` and `DifferentialGradedModule.coneTriangle` are made
`implicit_reducible` for this file.  Without that, `coneModule f` — which is `(cone f).module` —
and `(coneTriangle f).obj₃` — which is `(Pretriangulated.Triangle.mk …).obj₃` — are the same
object only after unfolding those two semireducible definitions, so every goal that mixes the
cone maps with the cone triangle is "not type-correct under the `implicit` transparency level"
and no `rw` or `simp only` fires inside it.  This is an attribute rather than a `set_option`, and
only the two declarations that need it are affected; the same device is used in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FlatSheafification.lean`. -/
attribute [local implicit_reducible] DifferentialGradedModule.cone
  DifferentialGradedModule.coneTriangle

namespace Stacks.DifferentialGradedModule.DeltaFunctor

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra.{u, v} R)

/-- The canonical functor from differential graded modules to their derived category: the
homotopy quotient followed by the localization at quasi-isomorphisms. -/
noncomputable abbrev canonicalFunctor :
    DifferentialGradedModule.{u, v, w} A ⥤ derivedCategory.{u, v, w} A :=
  toHomotopyCategory A ⋙ (quasiIsomorphisms A).Q

/-- The cone-to-quotient map `C(f) ⟶ X₃` of a short complex, sending a cone element to the
image of its first coordinate under `X₂ ⟶ X₃`. -/
private noncomputable def coneToQuotient
    (S : ShortComplex (DifferentialGradedModule.{u, v, w} A)) :
    coneModule S.f ⟶ S.X₃ := by
  let C := cone S.f
  refine
    { toFun := S.g.toFun.comp
        ((LinearMap.fst R S.X₂.M S.X₁.M).comp C.coordinates.toLinearMap)
      map_smul := ?_
      map_grading := ?_
      map_d := ?_ }
  · intro x a
    simp only [LinearMap.comp_apply, LinearMap.fst_apply]
    exact S.g.map_smul _ _
  · exact fun n x hx => S.g.map_grading n _ ((C.grading_iff n x).mp hx).1
  · apply LinearMap.ext
    intro x
    change S.g.toFun ((C.coordinates (C.module.d x)).1) =
      S.X₃.d (S.g.toFun (C.coordinates x).1)
    rw [C.differential]
    have hgd := LinearMap.congr_fun S.g.map_d (C.coordinates x).1
    rw [map_add]
    change (S.g.toFun ∘ₗ S.X₂.d) (C.coordinates x).1 +
      S.g.toFun (S.f.toFun (C.coordinates x).2) = _
    rw [hgd]
    have hfg : S.g.toFun (S.f.toFun (C.coordinates x).2) = 0 :=
      LinearMap.congr_fun (congrArg (fun z : S.X₁ ⟶ S.X₃ => z.toFun) S.zero) _
    rw [hfg, add_zero]
    rfl

/-- The map of cones induced by a morphism of short complexes. -/
private noncomputable def coneMap
    {S S' : ShortComplex (DifferentialGradedModule.{u, v, w} A)}
    (φ : S ⟶ S') : coneModule S.f ⟶ coneModule S'.f := by
  refine
    { toFun := LinearMap.prod
        (φ.τ₂.toFun.comp (LinearMap.fst R S.X₂.M S.X₁.M))
        (φ.τ₁.toFun.comp (LinearMap.snd R S.X₂.M S.X₁.M))
      map_smul := ?_
      map_grading := ?_
      map_d := ?_ }
  · intro x r
    change (φ.τ₂.toFun (MulOpposite.op r • x.1),
      φ.τ₁.toFun (MulOpposite.op r • x.2)) =
      MulOpposite.op r • (φ.τ₂.toFun x.1, φ.τ₁.toFun x.2)
    apply Prod.ext <;> simp [φ.τ₁.map_smul, φ.τ₂.map_smul]
  · intro n x hx
    have hx' := ((cone S.f).grading_iff n x).mp hx
    rw [(cone S'.f).grading_iff]
    change φ.τ₂.toFun x.1 ∈ S'.X₂.grading n ∧
      φ.τ₁.toFun x.2 ∈ S'.X₁.grading (n + 1)
    exact ⟨φ.τ₂.map_grading n x.1 hx'.1,
      φ.τ₁.map_grading (n + 1) x.2 hx'.2⟩
  · apply LinearMap.ext
    intro x
    change S.X₂.M × S.X₁.M at x
    change (φ.τ₂.toFun (S.X₂.d x.1 + S.f.toFun x.2),
        φ.τ₁.toFun (-S.X₁.d x.2)) =
      (S'.X₂.d (φ.τ₂.toFun x.1) + S'.f.toFun (φ.τ₁.toFun x.2),
        -S'.X₁.d (φ.τ₁.toFun x.2))
    have h12x := LinearMap.congr_fun (congrArg (fun g : S.X₁ ⟶ S'.X₂ => g.toFun) φ.comm₁₂) x.2
    have hd₂ := LinearMap.congr_fun φ.τ₂.map_d x.1
    have hd₁ := LinearMap.congr_fun φ.τ₁.map_d x.2
    change φ.τ₂.toFun (S.X₂.d x.1) = S'.X₂.d (φ.τ₂.toFun x.1) at hd₂
    change φ.τ₁.toFun (S.X₁.d x.2) = S'.X₁.d (φ.τ₁.toFun x.2) at hd₁
    change S'.f.toFun (φ.τ₁.toFun x.2) = φ.τ₂.toFun (S.f.toFun x.2) at h12x
    apply Prod.ext
    · simp only [map_add]
      rw [hd₂, ← h12x]
    · simp only [map_neg]
      rw [hd₁]

/-- In each degree, the cone of `f` is the product of the degree of `L` with the next degree
of `K`. -/
private noncomputable def coneGradingEquiv
    {K L : DifferentialGradedModule.{u, v, w} A} (f : K ⟶ L) (n : ℤ) :
    (cone f).module.grading n ≃ₗ[R]
      (L.toCochainComplex.X n × K.toCochainComplex.X (n + 1)) where
  toFun x :=
    (⟨((cone f).coordinates x).1, ((cone f).grading_iff n x).mp x.property |>.1⟩,
     ⟨((cone f).coordinates x).2, ((cone f).grading_iff n x).mp x.property |>.2⟩)
  invFun x :=
    ⟨(cone f).coordinates.symm (x.1.1, x.2.1),
      ((cone f).grading_iff n _).mpr ⟨x.1.2, x.2.2⟩⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by
    apply Prod.ext <;> apply Subtype.ext <;> simp
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      change ((cone f).coordinates x).1 + ((cone f).coordinates y).1 = _
      rfl
    · apply Subtype.ext
      change ((cone f).coordinates x).2 + ((cone f).coordinates y).2 = _
      rfl
  map_smul' r x := by
    apply Prod.ext
    · apply Subtype.ext
      change r • ((cone f).coordinates x).1 = _
      rfl
    · apply Subtype.ext
      change r • ((cone f).coordinates x).2 = _
      rfl

/-- The degreewise comparison between the underlying cochain complex of the cone and the mapping
cone of the underlying map. -/
private noncomputable def coneForgetXIso
    {K L : DifferentialGradedModule.{u, v, w} A} (f : K ⟶ L) (n : ℤ) :
    ((forgetToCochainComplex A).obj (coneModule f)).X n ≅
      (CochainComplex.mappingCone ((forgetToCochainComplex A).map f)).X n :=
  ((coneGradingEquiv A f n).trans
      (LinearEquiv.prodComm R (L.toCochainComplex.X n)
        (K.toCochainComplex.X (n + 1)))).toModuleIso ≪≫
    (ModuleCat.biprodIsoProd _ _).symm ≪≫
    (HomologicalComplex.homotopyCofiber.XIsoBiprod
      ((forgetToCochainComplex A).map f) n (n + 1) rfl).symm

/-- `coneForgetXIso` followed by the first mapping-cone coordinate is the second cone
coordinate. -/
private theorem coneForgetXIso_fst
    {K L : DifferentialGradedModule.{u, v, w} A} (f : K ⟶ L) (n : ℤ) :
    (coneForgetXIso A f n).hom ≫
      (CochainComplex.mappingCone.fst
        ((forgetToCochainComplex A).map f)).1.v n (n + 1) rfl =
    ModuleCat.ofHom ((LinearMap.snd R (L.toCochainComplex.X n)
      (K.toCochainComplex.X (n + 1))).comp (coneGradingEquiv A f n).toLinearMap) := by
  show (coneForgetXIso A f n).hom ≫
    HomologicalComplex.homotopyCofiber.fstX
      ((forgetToCochainComplex A).map f) n (n + 1) rfl = _
  let c := HomologicalComplex.homotopyCofiber.XIsoBiprod
    ((forgetToCochainComplex A).map f) n (n + 1) rfl
  show ((((coneGradingEquiv A f n).trans
      (LinearEquiv.prodComm R (L.toCochainComplex.X n)
        (K.toCochainComplex.X (n + 1)))).toModuleIso ≪≫
      (ModuleCat.biprodIsoProd _ _).symm ≪≫ c.symm).hom ≫ c.hom ≫
      Limits.biprod.fst) = _
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  have key : ((K.toCochainComplex.X (n + 1)).biprodIsoProd
        (L.toCochainComplex.X n)).inv ≫ Limits.biprod.fst =
      ModuleCat.ofHom (LinearMap.fst R (K.toCochainComplex.X (n + 1))
        (L.toCochainComplex.X n)) :=
    ModuleCat.biprodIsoProd_inv_comp_fst _ _
  refine Eq.trans (congrArg (fun m => _ ≫ m) key) ?_
  rfl

/-- `coneForgetXIso` followed by the second mapping-cone coordinate is the first cone
coordinate. -/
private theorem coneForgetXIso_snd
    {K L : DifferentialGradedModule.{u, v, w} A} (f : K ⟶ L) (n : ℤ) :
    (coneForgetXIso A f n).hom ≫
      (CochainComplex.mappingCone.snd
        ((forgetToCochainComplex A).map f)).v n n (by simp) =
    ModuleCat.ofHom ((LinearMap.fst R (L.toCochainComplex.X n)
      (K.toCochainComplex.X (n + 1))).comp (coneGradingEquiv A f n).toLinearMap) := by
  have hsnd : HomologicalComplex.homotopyCofiber.sndX
      ((forgetToCochainComplex A).map f) n =
      (HomologicalComplex.homotopyCofiber.XIsoBiprod
        ((forgetToCochainComplex A).map f) n (n + 1) rfl).hom ≫ Limits.biprod.snd := by
    have h : ∀ (j : ℤ) (h : (ComplexShape.up ℤ).Rel n j),
        HomologicalComplex.homotopyCofiber.sndX
            ((forgetToCochainComplex A).map f) n =
          (HomologicalComplex.homotopyCofiber.XIsoBiprod
            ((forgetToCochainComplex A).map f) n j h).hom ≫ Limits.biprod.snd := by
      intro j hrel
      obtain rfl := (ComplexShape.up ℤ).next_eq' hrel
      simp only [HomologicalComplex.homotopyCofiber.sndX, dite_eq_left hrel]
    exact h (n + 1) rfl
  show (coneForgetXIso A f n).hom ≫
    HomologicalComplex.homotopyCofiber.sndX
      ((forgetToCochainComplex A).map f) n = _
  rw [hsnd]
  let c := HomologicalComplex.homotopyCofiber.XIsoBiprod
    ((forgetToCochainComplex A).map f) n (n + 1) rfl
  show ((((coneGradingEquiv A f n).trans
      (LinearEquiv.prodComm R (L.toCochainComplex.X n)
        (K.toCochainComplex.X (n + 1)))).toModuleIso ≪≫
      (ModuleCat.biprodIsoProd _ _).symm ≪≫ c.symm).hom ≫ c.hom ≫
      Limits.biprod.snd) = _
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  have key : ((K.toCochainComplex.X (n + 1)).biprodIsoProd
        (L.toCochainComplex.X n)).inv ≫ Limits.biprod.snd =
      ModuleCat.ofHom (LinearMap.snd R (K.toCochainComplex.X (n + 1))
        (L.toCochainComplex.X n)) :=
    ModuleCat.biprodIsoProd_inv_comp_snd _ _
  refine Eq.trans (congrArg (fun m => _ ≫ m) key) ?_
  rfl

/-- The underlying cochain complex of the cone is the mapping cone of the underlying map. -/
private noncomputable def coneForgetIso
    {K L : DifferentialGradedModule.{u, v, w} A} (f : K ⟶ L) :
    (forgetToCochainComplex A).obj (coneModule f) ≅
      CochainComplex.mappingCone ((forgetToCochainComplex A).map f) := by
  refine HomologicalComplex.Hom.isoOfComponents (coneForgetXIso A f) ?_
  intro n m hnm
  obtain rfl : n + 1 = m := hnm
  rw [CochainComplex.mappingCone.ext_to_iff _ _ (n + 1 + 1) rfl]
  constructor
  · rw [Category.assoc, CochainComplex.mappingCone.d_fst_v _ _ _ _ rfl rfl,
      Preadditive.comp_neg, ← Category.assoc, coneForgetXIso_fst,
      Category.assoc, coneForgetXIso_fst]
    dsimp only [forgetToCochainComplex]
    simp only [toCochainComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (cone f).module.grading n at x
    apply Subtype.ext
    change -K.d ((cone f).coordinates x).2 =
      ((cone f).coordinates ((cone f).module.d x)).2
    rw [(cone f).differential]
  · rw [Category.assoc, CochainComplex.mappingCone.d_snd_v _ _ _ rfl,
      Preadditive.comp_add, ← Category.assoc, coneForgetXIso_fst,
      ← Category.assoc, coneForgetXIso_snd, Category.assoc, coneForgetXIso_snd]
    dsimp only [forgetToCochainComplex]
    simp only [toCochainComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (cone f).module.grading n at x
    apply Subtype.ext
    change f.toFun ((cone f).coordinates x).2 + L.d ((cone f).coordinates x).1 =
      ((cone f).coordinates ((cone f).module.d x)).1
    rw [(cone f).differential, add_comm]

/-- For a short exact sequence the cone-to-quotient map is a quasi-isomorphism. -/
private theorem coneToQuotient_quasiIso
    (S : ShortComplex (DifferentialGradedModule.{u, v, w} A)) (hS : S.ShortExact) :
    quasiIsomorphisms A ((toHomotopyCategory A).map (coneToQuotient A S)) := by
  rw [quasiIsomorphisms_map_iff]
  let F := forgetToCochainComplex A
  let S' := S.map F
  have hS' : S'.ShortExact := shortExact_forgetToCochainComplex (A := A) S hS
  have hdesc : QuasiIso (CochainComplex.mappingCone.descShortComplex S') :=
    CochainComplex.mappingCone.quasiIso_descShortComplex hS'
  have hcomp : F.map (coneToQuotient A S) =
      (coneForgetIso A S.f).hom ≫ CochainComplex.mappingCone.descShortComplex S' := by
    apply HomologicalComplex.Hom.ext
    funext n
    rw [HomologicalComplex.comp_f]
    dsimp only [CochainComplex.mappingCone.descShortComplex]
    rw [CochainComplex.mappingCone.desc_f (φ := S'.f) (α := 0) (β := S'.g) (eq := by simp)
      n (n + 1) rfl]
    show (F.map (coneToQuotient A S)).f n = (coneForgetXIso A S.f n).hom ≫ _
    simp only [CochainComplex.HomComplex.Cochain.zero_v, Limits.comp_zero, zero_add,
      ← Category.assoc, S', ShortComplex.map_f]
    rw [coneForgetXIso_snd A S.f n]
    rfl
  rw [hcomp]
  infer_instance

/-- The connecting morphism attached to a short exact sequence: the third arrow of the cone
triangle, read after inverting the cone-to-quotient quasi-isomorphism. -/
private noncomputable def connectingMap
    {S : ShortComplex (DifferentialGradedModule.{u, v, w} A)} (hS : S.ShortExact) :
    (canonicalFunctor.{u, v, w} A).obj S.X₃ ⟶ ((canonicalFunctor A).obj S.X₁)⟦(1 : ℤ)⟧ :=
  letI : IsIso ((canonicalFunctor A).map (coneToQuotient A S)) :=
    CategoryTheory.Localization.inverts (quasiIsomorphisms A).Q (quasiIsomorphisms A)
      ((toHomotopyCategory A).map (coneToQuotient A S)) (coneToQuotient_quasiIso A S hS)
  inv ((canonicalFunctor A).map (coneToQuotient A S)) ≫
    (quasiIsomorphisms A).Q.map (coneTriangle S.f).mor₃ ≫
      ((quasiIsomorphisms A).Q.commShiftIso (1 : ℤ)).hom.app
        ((toHomotopyCategory A).obj S.X₁)

/-- The cone-to-quotient map extends the map `X₂ ⟶ X₃` along the cone inclusion. -/
private theorem coneInclusion_comp_coneToQuotient
    (S : ShortComplex (DifferentialGradedModule.{u, v, w} A)) :
    coneInclusion S.f ≫ coneToQuotient A S = S.g := by
  apply DifferentialGradedModule.Hom.ext
  apply LinearMap.ext
  intro x
  show S.g.toFun ((cone S.f).coordinates ((cone S.f).inclusion.toFun x)).1 = S.g.toFun x
  rw [(cone S.f).inclusion_coordinates x]

/-- The cone map is compatible with the cone-to-quotient maps. -/
private theorem coneMap_comp_coneToQuotient
    {S S' : ShortComplex (DifferentialGradedModule.{u, v, w} A)} (φ : S ⟶ S') :
    coneMap (A := A) φ ≫ coneToQuotient A S' = coneToQuotient A S ≫ φ.τ₃ := by
  apply DifferentialGradedModule.Hom.ext
  apply LinearMap.ext
  intro x
  show S'.g.toFun (φ.τ₂.toFun ((cone S.f).coordinates x).1) =
    φ.τ₃.toFun (S.g.toFun ((cone S.f).coordinates x).1)
  exact LinearMap.congr_fun (congrArg (fun g : S.X₂ ⟶ S'.X₃ => g.toFun) φ.comm₂₃) _

/-- The cone map is compatible with the cone projections. -/
private theorem coneMap_comp_coneProjection
    {S S' : ShortComplex (DifferentialGradedModule.{u, v, w} A)} (φ : S ⟶ S') :
    coneMap (A := A) φ ≫ coneProjection S'.f =
      coneProjection S.f ≫ shiftMap φ.τ₁ 1 := by
  apply DifferentialGradedModule.Hom.ext
  apply LinearMap.ext
  intro x
  rfl

/-- The cone map is compatible with the projection-to-shift composite that is the third arrow of
the cone triangle.  Stated with its own explicit types, rather than reached by unfolding
`DifferentialGradedModule.coneTriangle` inside the goal: the vertices of a
`Pretriangulated.Triangle.mk` are not type-correct at `implicit` transparency once its arrows
have been unfolded, and no rewrite fires through that. -/
private theorem coneMap_comp_coneProjection_quotientShiftIso
    {S S' : ShortComplex (DifferentialGradedModule.{u, v, w} A)} (φ : S ⟶ S') :
    (toHomotopyCategory A).map (coneMap (A := A) φ) ≫
        ((toHomotopyCategory A).map (coneProjection S'.f) ≫
          (quotientShiftIso S'.X₁ 1).hom) =
      ((toHomotopyCategory A).map (coneProjection S.f) ≫
          (quotientShiftIso S.X₁ 1).hom) ≫
        ((toHomotopyCategory A).map φ.τ₁)⟦(1 : ℤ)⟧' := by
  rw [← Category.assoc, ← Functor.map_comp, coneMap_comp_coneProjection,
    Functor.map_comp, Category.assoc,
    quotient_map_shiftMap_comp_quotientShiftIso, ← Category.assoc]

/-- The cone map is compatible with the third arrows of the cone triangles. -/
private theorem coneMap_comp_coneTriangle_mor₃
    {S S' : ShortComplex (DifferentialGradedModule.{u, v, w} A)} (φ : S ⟶ S') :
    (toHomotopyCategory A).map (coneMap (A := A) φ) ≫ (coneTriangle S'.f).mor₃ =
      (coneTriangle S.f).mor₃ ≫ ((toHomotopyCategory A).map φ.τ₁)⟦(1 : ℤ)⟧' :=
  coneMap_comp_coneProjection_quotientShiftIso A φ

/-- Membership of the cone triangle in the distinguished triangles of the homotopy category:
the class is by definition the triangles isomorphic to a cone triangle. -/
private theorem coneTriangle_distinguished
    {K L : DifferentialGradedModule.{u, v, w} A} (f : K ⟶ L) :
    coneTriangle f ∈ Pretriangulated.distinguishedTriangles
      (C := HomotopyCategory.{u, v, w} A) :=
  ⟨K, L, f, ⟨Iso.refl _⟩⟩

/-- Localization of the cone-to-quotient map is invertible. -/
private theorem isIso_localization_coneToQuotient
    (S : ShortComplex (DifferentialGradedModule.{u, v, w} A)) (hS : S.ShortExact) :
    IsIso ((quasiIsomorphisms A).Q.map ((toHomotopyCategory A).map (coneToQuotient A S))) :=
  CategoryTheory.Localization.inverts (quasiIsomorphisms A).Q (quasiIsomorphisms A)
    ((toHomotopyCategory A).map (coneToQuotient A S)) (coneToQuotient_quasiIso A S hS)

/-- The second square of the comparison between the image of the cone triangle and the triangle
of the short exact sequence.  Stated with its own explicit types and discharged by `exact` at
the use site, because the triangle's vertices are not type-correct at `implicit` transparency
once its arrows have been unfolded. -/
private theorem localization_coneInclusion_comp_coneToQuotient
    (S : ShortComplex (DifferentialGradedModule.{u, v, w} A)) :
    (quasiIsomorphisms A).Q.map ((toHomotopyCategory A).map (coneInclusion S.f)) ≫
        (quasiIsomorphisms A).Q.map ((toHomotopyCategory A).map (coneToQuotient A S)) =
      (quasiIsomorphisms A).Q.map ((toHomotopyCategory A).map S.g) := by
  rw [← Functor.map_comp, ← Functor.map_comp, coneInclusion_comp_coneToQuotient]

/-- Localization of the cone-to-quotient map is invertible, in the spelling that reads the
localization through the canonical functor.  `Functor.comp` is semireducible, so this spelling
and `isIso_localization_coneToQuotient` are not interchangeable by instance search even though
they are definitionally the same morphism. -/
private theorem isIso_canonicalFunctor_coneToQuotient
    (S : ShortComplex (DifferentialGradedModule.{u, v, w} A)) (hS : S.ShortExact) :
    IsIso ((canonicalFunctor A).map (coneToQuotient A S)) :=
  CategoryTheory.Localization.inverts (quasiIsomorphisms A).Q (quasiIsomorphisms A)
    ((toHomotopyCategory A).map (coneToQuotient A S)) (coneToQuotient_quasiIso A S hS)

/-- The third square of the comparison: prefixing the connecting morphism with the localized
cone-to-quotient map cancels the inverse that the connecting morphism carries, returning the
localization of the third arrow of the cone triangle.  Stated with its own explicit types and
discharged by `exact` at the use site, rather than reached by rewriting inside the triangle
isomorphism's goal. -/
private theorem canonicalFunctor_coneToQuotient_comp_connectingMap
    {S : ShortComplex (DifferentialGradedModule.{u, v, w} A)} (hS : S.ShortExact) :
    (canonicalFunctor A).map (coneToQuotient A S) ≫ connectingMap A hS =
      (quasiIsomorphisms A).Q.map (coneTriangle S.f).mor₃ ≫
        ((quasiIsomorphisms A).Q.commShiftIso (1 : ℤ)).hom.app
          ((toHomotopyCategory A).obj S.X₁) :=
  let := isIso_canonicalFunctor_coneToQuotient A S hS
  IsIso.hom_inv_id_assoc _ _

/-- The `δ`-functor structure on the canonical functor. -/
private noncomputable def canonicalDeltaFunctor :
    (canonicalFunctor.{u, v, w} A).DeltaFunctorStructure
      (DifferentialGradedModule.{u, v, w} A) (derivedCategory.{u, v, w} A) := by
  refine
    { δ := fun {S} hS => connectingMap A hS
      distinguished := ?_
      δ_naturality := ?_ }
  · intro S hS
    have hInv := isIso_localization_coneToQuotient A S hS
    have hInv' := isIso_canonicalFunctor_coneToQuotient A S hS
    refine Pretriangulated.isomorphic_distinguished _
      ((quasiIsomorphisms A).Q.map_distinguished _ (coneTriangle_distinguished A S.f)) _ ?_
    refine Iso.symm (Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
      (@asIso _ _ _ _ ((quasiIsomorphisms A).Q.map
        ((toHomotopyCategory A).map (coneToQuotient A S))) hInv) ?_ ?_ ?_)
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact (Category.comp_id _).trans
        ((localization_coneInclusion_comp_coneToQuotient A S).trans
          (Category.id_comp _).symm)
    · have hid := (CategoryTheory.shiftFunctor (derivedCategory.{u, v, w} A) (1 : ℤ)).map_id
        ((quasiIsomorphisms A).Q.mapTriangle.obj (coneTriangle S.f)).obj₁
      exact (congrArg (fun m =>
            ((quasiIsomorphisms A).Q.mapTriangle.obj (coneTriangle S.f)).mor₃ ≫ m) hid).trans
        ((Category.comp_id _).trans
          (canonicalFunctor_coneToQuotient_comp_connectingMap A hS).symm)
  · intro S₁ S₂ h₁ h₂ φ
    have hInv₁ := isIso_localization_coneToQuotient A S₁ h₁
    have hInv₂ := isIso_localization_coneToQuotient A S₂ h₂
    have hInv₁' := isIso_canonicalFunctor_coneToQuotient A S₁ h₁
    have hInv₂' := isIso_canonicalFunctor_coneToQuotient A S₂ h₂
    have hq := congrArg ((canonicalFunctor A).map) (coneMap_comp_coneToQuotient A φ)
    simp only [Functor.map_comp, Functor.comp_map] at hq
    have hp : (quasiIsomorphisms A).Q.map ((toHomotopyCategory A).map (coneMap (A := A) φ)) ≫
          (quasiIsomorphisms A).Q.map (coneTriangle S₂.f).mor₃ =
        (quasiIsomorphisms A).Q.map (coneTriangle S₁.f).mor₃ ≫
          (quasiIsomorphisms A).Q.map (((toHomotopyCategory A).map φ.τ₁)⟦(1 : ℤ)⟧') :=
      (((quasiIsomorphisms A).Q.map_comp _ _).symm.trans
          (congrArg (quasiIsomorphisms A).Q.map
            (coneMap_comp_coneTriangle_mor₃ A φ))).trans
        ((quasiIsomorphisms A).Q.map_comp _ _)
    have hξ := ((quasiIsomorphisms A).Q.commShiftIso (1 : ℤ)).hom.naturality
      ((toHomotopyCategory A).map φ.τ₁)
    simp only [Functor.comp_map] at hξ
    dsimp only [connectingMap]
    apply (cancel_epi ((canonicalFunctor A).map (coneToQuotient A S₁))).mp
    simp only [Functor.comp_obj, Functor.comp_map, ← Category.assoc, IsIso.hom_inv_id,
      Category.id_comp]
    rw [Category.assoc, ← hξ, ← Category.assoc, ← hp, ← hq]
    simp only [Functor.comp_obj, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- **Stacks Project, Tag 09L0.** The canonical functor from differential graded modules to
their derived category is a `δ`-functor, with connecting arrow the third arrow of the cone
triangle read after inverting the cone-to-quotient quasi-isomorphism. -/
@[stacks 09L0]
theorem exists_deltaFunctorStructure_δ_eq :
    ∃ h : (canonicalFunctor.{u, v, w} A).DeltaFunctorStructure
        (DifferentialGradedModule.{u, v, w} A) (derivedCategory.{u, v, w} A),
      ∀ (S : ShortComplex (DifferentialGradedModule.{u, v, w} A)) (hS : S.ShortExact),
        ∃ q : coneModule S.f ⟶ S.X₃,
          (∀ x : (coneModule S.f).M,
            q.toFun x = S.g.toFun ((cone S.f).coordinates x).1) ∧
          (coneInclusion S.f ≫ q = S.g) ∧
          quasiIsomorphisms A ((toHomotopyCategory A).map q) ∧
          ∃ _ : IsIso ((canonicalFunctor A).map q),
            h.δ hS =
              inv ((canonicalFunctor A).map q) ≫
                (quasiIsomorphisms A).Q.map (coneTriangle S.f).mor₃ ≫
                  ((quasiIsomorphisms A).Q.commShiftIso (1 : ℤ)).hom.app
                    ((toHomotopyCategory A).obj S.X₁) :=
  ⟨canonicalDeltaFunctor A, fun S hS => ⟨coneToQuotient A S, fun _ => rfl,
    coneInclusion_comp_coneToQuotient A S, coneToQuotient_quasiIso A S hS,
    isIso_canonicalFunctor_coneToQuotient A S hS, rfl⟩⟩

end Stacks.DifferentialGradedModule.DeltaFunctor

end
