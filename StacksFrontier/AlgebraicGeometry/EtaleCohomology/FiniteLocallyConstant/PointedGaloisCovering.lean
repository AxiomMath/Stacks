module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.GaloisCoverDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.MonodromyModule
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleConnectedObjects
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleEquivalence
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.UnibranchLocallyIrreducible

/-!
# Pointed Galois covers of a geometrically unibranch scheme, and the monodromy module

Let `X` be an irreducible, geometrically unibranch scheme with a geometric point `x`. A pointed
Galois cover `A` of `X` is irreducible (it is connected and étale over `X`), so it is a Galois
covering of `X` with group `Aut(A)` in the sense of
`AlgebraicGeometry.EtaleGaloisCovering`.

If a sheaf of `Λ`-modules `F` on the small étale site of `X` is constant on `A`, its sections
over `A` already compute its monodromy module: the restriction maps `F(A) → F(B)` along the
morphisms of pointed Galois covers `B ⟶ A` are bijective, the sections of a constant sheaf over
an irreducible object being the constants.

## Main definitions

* `AlgebraicGeometry.PointedGaloisCover.etaleGaloisCovering` — the Galois covering of `X` with
  group `Aut(A)` underlying a pointed Galois cover.

## Main results

* `AlgebraicGeometry.bijective_map_of_iso_constantSheaf` — restriction of a sheaf constant on an
  irreducible object to an irreducible object over it is bijective.
* `AlgebraicGeometry.bijective_colimit_ι_monodromyDiagram` — for a sheaf constant on a pointed
  Galois cover `A`, the map `F(A) → Φ(F)` to the monodromy module is bijective.
* `AlgebraicGeometry.exists_pointedGaloisCover_subset` — the elements of `π₁` acting trivially
  on the pointed Galois covers form a basis of neighbourhoods of `1`.

## References

* [Stacks Project, Tag 0GIY](https://stacks.math.columbia.edu/tag/0GIY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite

universe u r

namespace AlgebraicGeometry

/-! ### Sheaves constant on an irreducible object -/

section Constant

variable {X : Scheme.{u}} (Λ : Type r) [Ring Λ]

/-- If `f ≫ g = h` with `g` and `h` bijective, then `f` is bijective. -/
private theorem bijective_of_comp_eq_of_bijective_right {R : Type*} [Ring R] {M N P : ModuleCat R}
    {f : M ⟶ N} {g : N ⟶ P} {h : M ⟶ P} (hfg : f ≫ g = h) (hg : Function.Bijective g)
    (hh : Function.Bijective h) : Function.Bijective f := by
  subst hfg
  exact (Function.Bijective.of_comp_iff' hg _).1 hh

/-- If `f ≫ g = h` with `f` and `h` bijective, then `g` is bijective. -/
private theorem bijective_of_comp_eq_of_bijective_left {R : Type*} [Ring R] {M N P : ModuleCat R}
    {f : M ⟶ N} {g : N ⟶ P} {h : M ⟶ P} (hfg : f ≫ g = h) (hf : Function.Bijective f)
    (hh : Function.Bijective h) : Function.Bijective g := by
  subst hfg
  exact (Function.Bijective.of_comp_iff _ hf).1 hh

/-- **The sections of a constant sheaf on the slice at an étale `X`-scheme `A`, over an object
with irreducible underlying scheme, are the constants.** -/
theorem bijective_toSheafify_over_const_app (M : ModuleCat.{max (u + 1) r} Λ) {A : X.Etale}
    (T : Over A) [IrreducibleSpace T.left.left] :
    Function.Bijective ((toSheafify (X.smallEtaleTopology.over A)
      ((Functor.const (Over A)ᵒᵖ).obj M)).app (op T)) := by
  have hiso : IsIso (((Stacks.ConstantSheaf.overPullbackConstantSheafIso
      X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ) A).hom.app M).hom.app (op T)) :=
    inferInstance
  exact bijective_of_comp_eq_of_bijective_right
    (Stacks.ConstantSheaf.toSheafify_overPullbackConstantSheafIso_app
      X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ) A M (op T))
    ((ConcreteCategory.isIso_iff_bijective _).1 hiso)
    (Scheme.bijective_toSheafify_const_app_of_irreducibleSpace Λ M T.left)

variable {Λ}

/-- **Restriction of a sheaf constant on an irreducible étale `X`-scheme `A` to an irreducible
étale `X`-scheme over `A` is bijective**: on both, the sections of the constant sheaf are the
constants. -/
theorem bijective_map_of_iso_constantSheaf
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)}
    {M : ModuleCat.{max (u + 1) r} Λ} {A : X.Etale} [IrreducibleSpace A.left]
    (e : (constantSheaf (X.smallEtaleTopology.over A) (ModuleCat.{max (u + 1) r} Λ)).obj M ≅
      (X.smallEtaleTopology.overPullback _ A).obj F)
    {B : X.Etale} [IrreducibleSpace B.left] (k : B ⟶ A) :
    Function.Bijective (F.obj.map k.op) := by
  let J := X.smallEtaleTopology.over A
  let T : Over A := Over.mk k
  let top : Over A := Over.mk (𝟙 A)
  let m : T ⟶ top := Over.homMk k (by simp [T, top])
  have : IrreducibleSpace T.left.left := inferInstanceAs (IrreducibleSpace B.left)
  have : IrreducibleSpace top.left.left := inferInstanceAs (IrreducibleSpace A.left)
  let C := ((constantSheaf J (ModuleCat.{max (u + 1) r} Λ)).obj M).obj
  have h1 : (toSheafify J ((Functor.const (Over A)ᵒᵖ).obj M)).app (op top) ≫ C.map m.op =
      (toSheafify J ((Functor.const (Over A)ᵒᵖ).obj M)).app (op T) := by
    have := (toSheafify J ((Functor.const (Over A)ᵒᵖ).obj M)).naturality m.op
    exact this.symm.trans (Category.id_comp _)
  have hC : Function.Bijective (C.map m.op) :=
    bijective_of_comp_eq_of_bijective_left h1 (bijective_toSheafify_over_const_app Λ M top)
      (bijective_toSheafify_over_const_app Λ M T)
  have htop : Function.Bijective (e.hom.hom.app (op top)) :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  have hhom : Function.Bijective (e.hom.hom.app (op T)) :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  exact bijective_of_comp_eq_of_bijective_left (e.hom.hom.naturality m.op).symm htop
    (hhom.comp hC)

end Constant

/-! ### Filtered colimits along bijective transition maps -/

/-- **In a filtered colimit, an object from which all transition maps are bijective maps
bijectively to the colimit.** -/
theorem bijective_colimit_ι_of_forall_bijective {R : Type*} [Ring R] {J : Type*} [Category J]
    [IsFiltered J] (D : J ⥤ ModuleCat.{r} R) [HasColimit D] [PreservesColimit D (forget _)]
    (j : J) (h : ∀ (k : J) (f : j ⟶ k), Function.Bijective (D.map f)) :
    Function.Bijective (colimit.ι D j) := by
  refine ⟨fun s t hst ↦ ?_, fun v ↦ ?_⟩
  · obtain ⟨k, f, g, hfg⟩ := Concrete.colimit_exists_of_rep_eq D s t hst
    let c := IsFiltered.coeqHom f g
    have hc : f ≫ c = g ≫ c := IsFiltered.coeq_condition f g
    have : D.map (f ≫ c) s = D.map (f ≫ c) t := by
      conv_rhs => rw [hc]
      rw [D.map_comp, D.map_comp, comp_apply, comp_apply, hfg]
    exact (h _ _).1 this
  · obtain ⟨k, s, rfl⟩ := Concrete.colimit_exists_rep D v
    let m := IsFiltered.max j k
    obtain ⟨t, ht⟩ := (h m (IsFiltered.leftToMax j k)).2 (D.map (IsFiltered.rightToMax j k) s)
    refine ⟨t, ?_⟩
    rw [← colimit.w D (IsFiltered.leftToMax j k), comp_apply, ht,
      ← colimit.w D (IsFiltered.rightToMax j k), comp_apply]

/-! ### Pointed Galois covers of a geometrically unibranch scheme -/

section Pointed

variable {X : Scheme.{u}} [IrreducibleSpace X] (hX : IsGeometricallyUnibranch X)
  (x : GeometricPoint X)

/-- A finite étale cover with nonempty source of a connected scheme is surjective: its image is
open and closed. -/
theorem surjective_hom_of_finiteEtaleOver {Y : Scheme.{u}} [ConnectedSpace Y]
    (A : FiniteEtaleOver Y) [hA : Nonempty A.left] : Function.Surjective A.hom.base := by
  have : PreconnectedSpace ((Functor.fromPUnit Y).obj A.right) :=
    inferInstanceAs (PreconnectedSpace Y)
  have : Nonempty ((𝟭 Scheme).obj A.left) := hA
  have ho : IsOpen (Set.range A.hom.base) := A.hom.isOpenMap.isOpen_range
  have hc : IsClosed (Set.range A.hom.base) := A.hom.isClosedMap.isClosed_range
  exact Set.range_eq_univ.1 (IsClopen.eq_univ ⟨hc, ho⟩ (Set.range_nonempty _))

variable {x}

/-- The underlying scheme of a pointed Galois cover is connected. -/
instance PointedGaloisCover.connectedSpace (A : PointedGaloisCover x) :
    ConnectedSpace A.obj.left :=
  connectedSpace_left_of_isConnected A.obj inferInstance

include hX in
/-- **The underlying scheme of a pointed Galois cover of an irreducible, geometrically unibranch
scheme is irreducible.** -/
theorem PointedGaloisCover.irreducibleSpace (A : PointedGaloisCover x) :
    IrreducibleSpace A.obj.left :=
  have : IrreducibleSpace ((Functor.fromPUnit X).obj A.obj.right) :=
    inferInstanceAs (IrreducibleSpace X)
  irreducibleSpace_of_etale_of_isGeometricallyUnibranch (X := X) A.obj.hom hX

/-- **A pointed Galois cover of an irreducible, geometrically unibranch scheme is a Galois
covering with group its automorphism group.** -/
def PointedGaloisCover.etaleGaloisCovering (A : PointedGaloisCover x) :
    EtaleGaloisCovering X (Aut A.obj) where
  cover := (PointedGaloisCover.toEtale x).obj A
  act h := h.hom.left
  act_comp_hom h := MorphismProperty.Over.w h.hom
  act_one := rfl
  act_mul _ _ := rfl
  surjective := surjective_hom_of_finiteEtaleOver A.obj
  irreducibleSpace := A.irreducibleSpace hX
  exists_mem_agreeLocus a b hab w := exists_aut_mem_agreeLocus a b hab w
  eq_of_comp_eq c _ _ hc := aut_eq_of_comp_eq c hc

/-- The cover underlying `PointedGaloisCover.etaleGaloisCovering` is the étale cover of `A`. -/
@[simp]
theorem PointedGaloisCover.etaleGaloisCovering_cover (A : PointedGaloisCover x) :
    (A.etaleGaloisCovering hX).cover = (PointedGaloisCover.toEtale x).obj A :=
  rfl

/-- In `PointedGaloisCover.etaleGaloisCovering`, an automorphism `h` of `A` acts by the étale
morphism underlying `h`. -/
@[simp]
theorem PointedGaloisCover.etaleGaloisCovering_actHom (A : PointedGaloisCover x)
    (h : Aut A.obj) :
    (A.etaleGaloisCovering hX).actHom h = (finiteEtaleToEtale X).map h.hom :=
  rfl

variable (x) in
/-- **The elements of `π₁` acting trivially on the pointed Galois covers form a basis of
neighbourhoods of `1`**: every neighbourhood of `1` contains the elements acting trivially on
some pointed Galois cover. -/
theorem exists_pointedGaloisCover_subset {U : Set (EtaleFundamentalGroup X x)}
    (hU : U ∈ nhds 1) :
    ∃ A : PointedGaloisCover x, {σ | galoisAut x σ A = 1} ⊆ U := by
  let e := autContinuousMulEquivEtaleFundamentalGroup X x
  have hU' : e ⁻¹' U ∈ nhds (1 : Aut (finiteEtaleFiberFintypeFunctor X x)) := by
    refine e.continuous.continuousAt.preimage_mem_nhds ?_
    have h1 : e 1 = 1 := e.toMulEquiv.map_one
    show U ∈ nhds (e 1)
    rw [h1]
    exact hU
  obtain ⟨A, -, hA⟩ := (nhds_one_has_basis_stabilizers _).mem_iff.1 hU'
  refine ⟨A, fun σ hσ ↦ ?_⟩
  have hσ' : e.symm σ ∈ MulAction.stabilizer _ A.pt := by
    rw [MulAction.mem_stabilizer_iff]
    have h := (galoisAut_eq_one_iff x σ A).1 hσ
    rw [← galoisAutHom_pt] at h
    have h2 := autMulEquivAutGalois_π (finiteEtaleFiberFintypeFunctor X x) (e.symm σ) A.obj A.pt
    exact h2.symm.trans (h.trans rfl)
  have := hA hσ'
  simpa using this

end Pointed

/-! ### The monodromy module of a sheaf constant on a pointed Galois cover -/

section Monodromy

variable {X : Scheme.{u}} [IrreducibleSpace X] (hX : IsGeometricallyUnibranch X)
  {x : GeometricPoint X} {Λ : Type r} [Ring Λ]

include hX in
/-- **The restriction maps of a sheaf constant on a pointed Galois cover `A`, along the morphisms
of pointed Galois covers into `A`, are bijective.** -/
theorem bijective_monodromyDiagram_map
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)}
    {M : ModuleCat.{max (u + 1) r} Λ} {A : PointedGaloisCover x}
    (e : (constantSheaf (X.smallEtaleTopology.over ((PointedGaloisCover.toEtale x).obj A))
      (ModuleCat.{max (u + 1) r} Λ)).obj M ≅
        (X.smallEtaleTopology.overPullback _ ((PointedGaloisCover.toEtale x).obj A)).obj F)
    {B : (PointedGaloisCover x)ᵒᵖ} (f : op A ⟶ B) :
    Function.Bijective (((monodromyDiagram x).obj F.obj).map f) := by
  have : IrreducibleSpace ((PointedGaloisCover.toEtale x).obj A).left := A.irreducibleSpace hX
  have : IrreducibleSpace ((PointedGaloisCover.toEtale x).obj B.unop).left :=
    B.unop.irreducibleSpace hX
  exact bijective_map_of_iso_constantSheaf e ((PointedGaloisCover.toEtale x).map f.unop)

include hX in
/-- **For a sheaf constant on a pointed Galois cover `A`, the map from its sections over `A` to
its monodromy module is bijective.** -/
theorem bijective_colimit_ι_monodromyDiagram
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)}
    {M : ModuleCat.{max (u + 1) r} Λ} {A : PointedGaloisCover x}
    (e : (constantSheaf (X.smallEtaleTopology.over ((PointedGaloisCover.toEtale x).obj A))
      (ModuleCat.{max (u + 1) r} Λ)).obj M ≅
        (X.smallEtaleTopology.overPullback _ ((PointedGaloisCover.toEtale x).obj A)).obj F) :
    Function.Bijective (colimit.ι ((monodromyDiagram x).obj F.obj) (op A)) :=
  bijective_colimit_ι_of_forall_bijective _ _ fun _ f ↦ bijective_monodromyDiagram_map hX e f

end Monodromy

end AlgebraicGeometry

end
