module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Topology.Sheaves.LocallySurjective
public import StacksFrontier.Cotangent.DirectedColimit
public import StacksFrontier.Cotangent.SheavesOfRings.AffineCotangentRestriction
public import StacksFrontier.Cotangent.SheavesOfRings.FundamentalTriangle
public import StacksFrontier.Cotangent.SheavesOfRings.SectionsComparisonSquareNaturality
public import StacksFrontier.Cotangent.SheavesOfRings.SectionwiseSheafification
public import StacksFrontier.Cotangent.Triangle.ProductDescent

/-!
# The change-of-base map of a tower of sheaves of rings, tested on stalks

Let `X` be a topological space and let `A ⟶ B ⟶ D` be homomorphisms of sheaves of commutative
rings on `X`. This file proves that the change-of-base-ring map `L_{D/A} ⟶ L_{D/B}` of
`CategoryTheory.Sheaf.towerCotangentChangeOfBase` is a quasi-isomorphism as soon as, at every
point `x`, the cotangent complex `L_{B_x/A_x}` of the map of stalk rings vanishes.

## Main definitions

* `CategoryTheory.Sheaf.stalkAlgebra`: the stalk `B_x` as an algebra over `A_x`.
* `CategoryTheory.Sheaf.stalkCotangentComplex`: the comparison of the stalk at `x` of the
  presheaf `U ↦ L_{B(U)/A(U)}` with `L_{B_x/A_x}`, an isomorphism of complexes.
* `CategoryTheory.Sheaf.sectionwiseChangeOfBase`: the sectionwise change-of-base map
  `U ↦ (L_{D(U)/A(U)} ⟶ L_{D(U)/B(U)})`.

## Main results

* `CommAlgCat.quasiIso_cotangentComplexBaseRingMap_of_isZero`: for ring maps `A → B → C` with
  `L_{B/A} = 0`, the map `L_{C/A} ⟶ L_{C/B}` is a quasi-isomorphism.
* `TopCat.Presheaf.W_of_bijective_stalkFunctor_map`: a map of presheaves of abelian groups on a
  space which is bijective on stalks is inverted by sheafification.
* `CategoryTheory.Sheaf.quasiIso_of_sectionwise_homology`: a map of complexes of sheaves of
  abelian groups which is covered by a map of complexes of presheaves whose maps on homology are
  inverted by sheafification is a quasi-isomorphism.
* `CategoryTheory.Sheaf.isIso_stalkCotangentComplex`: the stalk of `U ↦ L_{B(U)/A(U)}` at `x` is
  `L_{B_x/A_x}`.
* `CategoryTheory.Sheaf.quasiIso_towerCotangentChangeOfBase_of_isZero_stalk`:
  `L_{D/A} ⟶ L_{D/B}` is a quasi-isomorphism when every `L_{B_x/A_x}` vanishes.

## Implementation notes

Stalks are indexed by `(OpenNhds x)ᵒᵈ`, a directed order, so that the elementwise colimit
criterion `IsDirectedColimitOfTypes` applies to the system of restriction squares; the germ maps
are its colimit cocone.

## References

* [Stacks Project, Tag 08S9](https://stacks.math.columbia.edu/tag/08S9)
* [Stacks Project, Tag 08SX](https://stacks.math.columbia.edu/tag/08SX)
* [Stacks Project, Tag 08T0](https://stacks.math.columbia.edu/tag/08T0)
* [Stacks Project, Tag 08QX](https://stacks.math.columbia.edu/tag/08QX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open TopologicalSpace

universe u

namespace CommAlgCat

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
  (C : Type u) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/-- **The change of base ring along a map with vanishing cotangent complex.** For ring maps
`A → B → C` with `L_{B/A} = 0`, the canonical map `L_{C/A} ⟶ L_{C/B}` is a quasi-isomorphism. -/
theorem quasiIso_cotangentComplexBaseRingMap_of_isZero
    (h : IsZero (cotangentComplexDerived.{u, u} A (CommAlgCat.of A B))) :
    QuasiIso (cotangentComplexBaseRingMap A B C) := by
  have h₁ : IsZero (fundamentalVertex₁.{u, u, u + 1, u + 1} A B C) :=
    Functor.map_isZero _ h
  have := (Triangle.isZero₁_iff_isIso₂ _ (productFundamentalTriangle_distinguished A B C)).1 h₁
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 this

/-- For ring maps `A → B → C` with `L_{B/A} = 0`, the map `L_{C/A} ⟶ L_{C/B}` of underlying
complexes of abelian groups is a quasi-isomorphism. -/
theorem quasiIso_cotangentComplexAbMap_displaySquare₂_of_isZero
    (h : IsZero (cotangentComplexDerived.{u, u} A (CommAlgCat.of A B))) :
    QuasiIso (cotangentComplexAbMap.{u, u, u} (displaySquare₂ A B C)) := by
  have := quasiIso_cotangentComplexBaseRingMap_of_isZero A B C h
  exact (inferInstance : QuasiIso (((forget₂ (ModuleCat.{u} C)
    AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (cotangentComplexBaseRingMap A B C)))

end CommAlgCat

namespace TopCat.Presheaf

variable {X : TopCat.{u}}

/-- A map of presheaves of abelian groups on a space which is injective on stalks is locally
injective. -/
theorem isLocallyInjective_of_injective_stalkFunctor_map
    {P Q : X.Presheaf AddCommGrpCat.{u}} (ψ : P ⟶ Q)
    (h : ∀ x : X, Function.Injective ((stalkFunctor AddCommGrpCat.{u} x).map ψ)) :
    CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) ψ := by
  constructor
  intro U s t hst x hx
  have hgerm : P.germ U.unop x hx s = P.germ U.unop x hx t := h x (by
    rw [stalkFunctor_map_germ_apply, stalkFunctor_map_germ_apply]
    exact congrArg _ hst)
  obtain ⟨W, hxW, iU, iV, e⟩ := P.germ_eq x hx hx s t hgerm
  refine ⟨W, iU, ?_, hxW⟩
  rwa [Subsingleton.elim iV iU] at e

/-- A map of presheaves of abelian groups on a space which is bijective on stalks is inverted by
sheafification. -/
theorem W_of_bijective_stalkFunctor_map
    {P Q : X.Presheaf AddCommGrpCat.{u}} (ψ : P ⟶ Q)
    (h : ∀ x : X, Function.Bijective ((stalkFunctor AddCommGrpCat.{u} x).map ψ)) :
    (Opens.grothendieckTopology X).W ψ := by
  rw [GrothendieckTopology.W_iff_isLocallyBijective]
  exact ⟨isLocallyInjective_of_injective_stalkFunctor_map ψ fun x => (h x).1,
    (locally_surjective_iff_surjective_on_stalks ψ).2 fun x => (h x).2⟩

/-- The stalk functor at `x` on presheaves of abelian groups, as a functor on
`(Opens X)ᵒᵖ ⥤ AddCommGrpCat`. -/
noncomputable abbrev stalkAb (x : X) : ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u} :=
  stalkFunctor AddCommGrpCat.{u} x

/-- Taking stalks of presheaves of abelian groups is left exact. -/
instance (x : X) : PreservesFiniteLimits (stalkAb x) := by
  change PreservesFiniteLimits
    ((Functor.whiskeringLeft _ _ _).obj (OpenNhds.inclusion x).op ⋙ colim)
  infer_instance

/-- Taking stalks of presheaves of abelian groups is right exact. -/
instance (x : X) : PreservesFiniteColimits (stalkAb x) := by
  change PreservesFiniteColimits
    ((Functor.whiskeringLeft _ _ _).obj (OpenNhds.inclusion x).op ⋙ colim)
  infer_instance

/-- Taking stalks of presheaves of abelian groups preserves zero morphisms. -/
instance (x : X) : (stalkAb x).PreservesZeroMorphisms := by
  change ((Functor.whiskeringLeft _ _ _).obj (OpenNhds.inclusion x).op ⋙
    colim).PreservesZeroMorphisms
  infer_instance

end TopCat.Presheaf

namespace CategoryTheory.Sheaf

universe v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- A functor preserving homology sends the homology map of `φ` to an isomorphism iff the homology
map of the image complex map is one. -/
private theorem isIso_map_homologyMap_iff {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [CategoryWithHomology C] [CategoryWithHomology D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.PreservesHomology]
    {K L : CochainComplex C ℤ} (φ : K ⟶ L) (n : ℤ) :
    IsIso (HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) n)
      ↔ IsIso (F.map (HomologicalComplex.homologyMap φ n)) :=
  (NatIso.isIso_map_iff (ShortComplex.homologyFunctorIso F)
    ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℤ) n).map φ))

/-- **Quasi-isomorphisms of complexes of sheaves are detected on sectionwise homology, up to
sheafification.** Let `φ : K ⟶ K'` be a map of complexes of sheaves of abelian groups, and let
`K₀ ⟶ K`, `K₀' ⟶ K'` be maps from complexes of presheaves of abelian groups which are, in every
degree, inverted by sheafification. If a map `φ₀ : K₀ ⟶ K₀'` compatible with `φ` induces, in
every degree, a map of homology presheaves which is inverted by sheafification, then `φ` is a
quasi-isomorphism. -/
theorem quasiIso_of_sectionwise_homology
    {K K' : CochainComplex (Sheaf J AddCommGrpCat.{max u v w}) ℤ}
    {K₀ K₀' : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) ℤ}
    (a : K₀ ⟶ ((sheafToPresheaf J _).mapHomologicalComplex _).obj K)
    (a' : K₀' ⟶ ((sheafToPresheaf J _).mapHomologicalComplex _).obj K')
    (ha : ∀ n, J.W (a.f n)) (ha' : ∀ n, J.W (a'.f n))
    (φ : K ⟶ K') (φ₀ : K₀ ⟶ K₀')
    (hcomm : φ₀ ≫ a' = a ≫ ((sheafToPresheaf J _).mapHomologicalComplex _).map φ)
    (hφ₀ : ∀ n, J.W (HomologicalComplex.homologyMap φ₀ n)) : QuasiIso φ := by
  let F := presheafToSheaf J AddCommGrpCat.{max u v w}
  let ι := sheafToPresheaf J AddCommGrpCat.{max u v w}
  have hiso : ∀ {P Q : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) ℤ} (b : P ⟶ Q),
      (∀ n, J.W (b.f n)) → IsIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map b) :=
    fun b hb => by
      have : ∀ n, IsIso (((F.mapHomologicalComplex (ComplexShape.up ℤ)).map b).f n) :=
        fun n => isIso_presheafToSheaf_map_of_W J _ (hb n)
      exact HomologicalComplex.Hom.isIso_of_components _
  have := hiso a ha
  have := hiso a' ha'
  have : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ₀) := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    have hF : IsIso (F.map (HomologicalComplex.homologyMap φ₀ n)) :=
      isIso_presheafToSheaf_map_of_W J _ (hφ₀ n)
    exact (isIso_map_homologyMap_iff F φ₀ n).2 hF
  have h₁ : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ₀ ≫
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).map a') := inferInstance
  rw [← Functor.map_comp, hcomm, Functor.map_comp] at h₁
  have h₂ : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((ι.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)) :=
    (quasiIso_iff_comp_left _ _).mp h₁
  let e : ι ⋙ F ≅ 𝟭 _ := asIso (sheafificationAdjunction J AddCommGrpCat.{max u v w}).counit
  let E := NatIso.mapHomologicalComplex e (ComplexShape.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)
  exact (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk (E.app K) (E.app K')
    (E.hom.naturality φ).symm)).mp h₂

end CategoryTheory.Sheaf

namespace CategoryTheory.Sheaf

section Stalk

variable {X : TopCat.{u}}

/-- The open set of a neighbourhood of `x`, read in the order dual. -/
abbrev nbhd {x : X} (i : (OpenNhds x)ᵒᵈ) : Opens X := (OrderDual.ofDual i).1

/-- A neighbourhood of `x` contains `x`. -/
lemma mem_nbhd {x : X} (i : (OpenNhds x)ᵒᵈ) : x ∈ nbhd i := (OrderDual.ofDual i).2

/-- The restriction from a neighbourhood to a smaller one. -/
abbrev nbhdHom {x : X} {i j : (OpenNhds x)ᵒᵈ} (h : i ≤ j) : op (nbhd i) ⟶ op (nbhd j) :=
  (homOfLE (show nbhd j ≤ nbhd i from h)).op

/-- The germ maps exhibit the stalk of a presheaf of commutative rings as the directed colimit of
its sections over the neighbourhoods of `x`. -/
theorem isDirectedColimitOfTypes_germ (F : (Opens X)ᵒᵖ ⥤ CommRingCat.{u}) (x : X) :
    IsDirectedColimitOfTypes (I := (OpenNhds x)ᵒᵈ)
      (fun _ _ h a => (F.map (nbhdHom h)).hom a)
      (fun i a => (TopCat.Presheaf.germ F (nbhd i) x (mem_nbhd i)).hom a) where
  map_id i a := by
    change (F.map (𝟙 _)).hom a = a
    rw [F.map_id]
    rfl
  map_comp i j k hij hjk a := by
    change (F.map (nbhdHom hij) ≫ F.map (nbhdHom hjk)).hom a = _
    rw [← F.map_comp]
    rfl
  comp i j hij a := TopCat.Presheaf.germ_res_apply F _ x (mem_nbhd j) a
  jointly_surjective b := by
    obtain ⟨U, hU, a, ha⟩ := TopCat.Presheaf.exists_germ_eq F b
    exact ⟨OrderDual.toDual ⟨U, hU⟩, a, ha⟩
  exists_eq i a b h := by
    obtain ⟨W, hW, iU, iV, e⟩ := TopCat.Presheaf.germ_eq F x (mem_nbhd i) (mem_nbhd i) a b h
    refine ⟨OrderDual.toDual ⟨W, hW⟩, iU.le, ?_⟩
    rwa [Subsingleton.elim iV iU] at e

variable {A B : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}} (f : A ⟶ B) (x : X)

/-- The stalk `A_x` of a sheaf of commutative rings on a space. -/
noncomputable abbrev stalkRing (A : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) :
    CommRingCat.{u} :=
  TopCat.Presheaf.stalk (X := X) A.obj x

/-- The ring map `A_x → B_x` on stalks. -/
noncomputable abbrev stalkMap : stalkRing x A ⟶ stalkRing x B :=
  (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map f.hom

/-- The stalk `B_x`, an algebra over `A_x` along the map of stalks. -/
noncomputable def stalkAlgebra : CommAlgCat.{u} (stalkRing x A) :=
  letI : Algebra (stalkRing x A) (stalkRing x B) := (stalkMap f x).hom.toAlgebra
  CommAlgCat.of (stalkRing x A) (stalkRing x B)

/-- The square of ring maps from the sections over a neighbourhood of `x` to the stalks. -/
noncomputable def germSquare (i : (OpenNhds x)ᵒᵈ) :
    CommAlgCat.AlgebraSquare.{u, u, u} (A.obj.obj (op (nbhd i))) (stalkRing x A)
      (sectionsAlgebra _ f (op (nbhd i))) (stalkAlgebra f x) where
  base := (TopCat.Presheaf.germ A.obj (nbhd i) x (mem_nbhd i)).hom
  map := (TopCat.Presheaf.germ B.obj (nbhd i) x (mem_nbhd i)).hom
  map_algebraMap a :=
    (TopCat.Presheaf.stalkFunctor_map_germ_apply (nbhd i) x (mem_nbhd i) f.hom a).symm

/-- The system of restriction squares over the neighbourhoods of `x`. -/
noncomputable abbrev nbhdSquare {i j : (OpenNhds x)ᵒᵈ} (h : i ≤ j) :=
  sectionsRestrictionSquare (Opens.grothendieckTopology X) f (nbhdHom h)

/-- The maps induced by the germ squares exhibit `L_{B_x/A_x}` as the
directed colimit of the `L_{B(U)/A(U)}` over the neighbourhoods `U` of `x`, in every degree. -/
theorem isDirectedColimitOfTypes_stalkCotangent (n : ℤ) :
    IsDirectedColimitOfTypes (I := (OpenNhds x)ᵒᵈ)
      (fun _ _ h a => (CommAlgCat.cotangentComplexAbMap (nbhdSquare f x h)).f n a)
      (fun i a => (CommAlgCat.cotangentComplexAbMap (germSquare f x i)).f n a) :=
  CommAlgCat.isDirectedColimitOfTypes_cotangentComplexAb.{u, u, u, _}
    (fun _ _ h => nbhdSquare f x h) (germSquare f x)
    (isDirectedColimitOfTypes_germ A.obj x) (isDirectedColimitOfTypes_germ B.obj x) n

/-- The presheaf `U ↦ L^n_{B(U)/A(U)}` restricted to the neighbourhoods of `x`. -/
noncomputable abbrev nbhdTerm (n : ℤ) : (OpenNhds x)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (OpenNhds.inclusion x).op ⋙
    (sectionwiseCotangentPresheafComplex (Opens.grothendieckTopology X) f).X n

/-- The cocone on the neighbourhoods of `x` whose legs are the maps induced by the germ
squares. -/
noncomputable def stalkCotangentCocone (n : ℤ) : Cocone (nbhdTerm f x n) where
  pt := (CommAlgCat.cotangentComplexAb (stalkRing x A) (stalkAlgebra f x)).X n
  ι :=
    { app U := (CommAlgCat.cotangentComplexAbMap (germSquare f x (OrderDual.toDual U.unop))).f n
      naturality U V φ := by
        ext a
        exact (isDirectedColimitOfTypes_stalkCotangent f x n).comp
          (OrderDual.toDual U.unop) (OrderDual.toDual V.unop) φ.unop.le a }

/-- The map from the stalk at `x` of `U ↦ L^n_{B(U)/A(U)}` to `L^n_{B_x/A_x}`. -/
noncomputable def stalkCotangentTerm (n : ℤ) :
    (TopCat.Presheaf.stalkAb x).obj
        ((sectionwiseCotangentPresheafComplex (Opens.grothendieckTopology X) f).X n) ⟶
      (CommAlgCat.cotangentComplexAb (stalkRing x A) (stalkAlgebra f x)).X n :=
  colimit.desc (nbhdTerm f x n) (stalkCotangentCocone f x n)

/-- The comparison of stalks restricted to the sections over a neighbourhood is the map induced by
the germ square. -/
theorem stalkCotangentTerm_germ (n : ℤ) (i : (OpenNhds x)ᵒᵈ) :
    TopCat.Presheaf.germ ((sectionwiseCotangentPresheafComplex (Opens.grothendieckTopology X)
        f).X n) (nbhd i) x (mem_nbhd i) ≫ stalkCotangentTerm f x n =
      (CommAlgCat.cotangentComplexAbMap (germSquare f x i)).f n :=
  colimit.ι_desc (stalkCotangentCocone f x n) (op (OrderDual.ofDual i))

/-- The comparison `(U ↦ L^n_{B(U)/A(U)})_x ⟶ L^n_{B_x/A_x}` is bijective. -/
theorem bijective_stalkCotangentTerm (n : ℤ) :
    Function.Bijective (stalkCotangentTerm f x n) := by
  have hL := isDirectedColimitOfTypes_stalkCotangent f x n
  let F := (sectionwiseCotangentPresheafComplex (Opens.grothendieckTopology X) f).X n
  have hg (i : (OpenNhds x)ᵒᵈ) (a) : stalkCotangentTerm f x n
      (TopCat.Presheaf.germ F (nbhd i) x (mem_nbhd i) a) =
        (CommAlgCat.cotangentComplexAbMap (germSquare f x i)).f n a :=
    ConcreteCategory.congr_hom (stalkCotangentTerm_germ f x n i) a
  refine ⟨fun s t hst => ?_, fun b => ?_⟩
  · obtain ⟨U, hU, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq F s
    obtain ⟨V, hV, b, rfl⟩ := TopCat.Presheaf.exists_germ_eq F t
    let k : (OpenNhds x)ᵒᵈ := OrderDual.toDual ⟨U ⊓ V, ⟨hU, hV⟩⟩
    have hkU : OrderDual.toDual (⟨U, hU⟩ : OpenNhds x) ≤ k := show U ⊓ V ≤ U from inf_le_left
    have hkV : OrderDual.toDual (⟨V, hV⟩ : OpenNhds x) ≤ k := show U ⊓ V ≤ V from inf_le_right
    have ea : TopCat.Presheaf.germ F U x hU a =
        TopCat.Presheaf.germ F (nbhd k) x (mem_nbhd k) (F.map (nbhdHom hkU) a) :=
      (TopCat.Presheaf.germ_res_apply F _ x (mem_nbhd k) a).symm
    have eb : TopCat.Presheaf.germ F V x hV b =
        TopCat.Presheaf.germ F (nbhd k) x (mem_nbhd k) (F.map (nbhdHom hkV) b) :=
      (TopCat.Presheaf.germ_res_apply F _ x (mem_nbhd k) b).symm
    rw [ea, eb] at hst ⊢
    rw [hg, hg] at hst
    obtain ⟨l, hkl, e⟩ := hL.exists_eq k _ _ hst
    rw [← TopCat.Presheaf.germ_res_apply F (homOfLE (show nbhd l ≤ nbhd k from hkl)) x
        (mem_nbhd l), ← TopCat.Presheaf.germ_res_apply F (homOfLE (show nbhd l ≤ nbhd k from hkl))
        x (mem_nbhd l)]
    exact congrArg _ e
  · obtain ⟨i, a, rfl⟩ := hL.jointly_surjective b
    exact ⟨_, hg i a⟩

/-- The comparison `(U ↦ L^n_{B(U)/A(U)})_x ⟶ L^n_{B_x/A_x}` is an isomorphism. -/
instance (n : ℤ) : IsIso (stalkCotangentTerm f x n) :=
  (ConcreteCategory.isIso_iff_bijective _).2 (bijective_stalkCotangentTerm f x n)

/-- The map from the stalk at `x` of the presheaf of complexes `U ↦ L_{B(U)/A(U)}` to
`L_{B_x/A_x}`. -/
noncomputable def stalkCotangentComplex :
    ((TopCat.Presheaf.stalkAb x).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (sectionwiseCotangentPresheafComplex (Opens.grothendieckTopology X) f) ⟶
      CommAlgCat.cotangentComplexAb (stalkRing x A) (stalkAlgebra f x) where
  f n := stalkCotangentTerm f x n
  comm' i j _ := by
    apply TopCat.Presheaf.stalk_hom_ext
    intro U hU
    have hi := stalkCotangentTerm_germ f x i (OrderDual.toDual ⟨U, hU⟩)
    have hj := stalkCotangentTerm_germ f x j (OrderDual.toDual ⟨U, hU⟩)
    refine Eq.symm ?_
    change TopCat.Presheaf.germ _ U x hU ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((sectionwiseCotangentPresheafComplex (Opens.grothendieckTopology X) f).d i j) ≫
          stalkCotangentTerm f x j = _
    rw [TopCat.Presheaf.stalkFunctor_map_germ_assoc]
    exact (congrArg (fun t => ((sectionwiseCotangentPresheafComplex (Opens.grothendieckTopology X)
        f).d i j).app (op U) ≫ t) hj).trans
      (((CommAlgCat.cotangentComplexAbMap (germSquare f x (OrderDual.toDual ⟨U, hU⟩))).comm
        i j).symm.trans ((congrArg (fun t => t ≫ _) hi.symm).trans (Category.assoc _ _ _)))

/-- **The stalk of the sectionwise cotangent complex is the cotangent complex of the stalks.**
The stalk at `x` of the presheaf of complexes `U ↦ L_{B(U)/A(U)}` is `L_{B_x/A_x}`. -/
theorem isIso_stalkCotangentComplex : IsIso (stalkCotangentComplex f x) := by
  have : ∀ n, IsIso ((stalkCotangentComplex f x).f n) := fun n =>
    (inferInstance : IsIso (stalkCotangentTerm f x n))
  exact HomologicalComplex.Hom.isIso_of_components _

end Stalk

section Tower

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} {A B D : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  (g : A ⟶ B) (h : B ⟶ D)

/-- The map of presheaves of complexes `U ↦ (L_{D(U)/A(U)} ⟶ L_{D(U)/B(U)})` induced by the
squares of ring maps on sections. -/
noncomputable def sectionwiseChangeOfBase :
    sectionwiseCotangentPresheafComplex (Opens.grothendieckTopology X) (g ≫ h) ⟶
      sectionwiseCotangentPresheafComplex (Opens.grothendieckTopology X) h where
  f n :=
    { app U := (CommAlgCat.cotangentComplexAbMap
        (sectionsSquare (Opens.grothendieckTopology X) g (𝟙 D) (Category.comp_id _) U)).f n
      naturality U V ι := by
        have e : (sectionsRestrictionSquare (Opens.grothendieckTopology X) (g ≫ h) ι).comp
            (sectionsSquare (Opens.grothendieckTopology X) g (𝟙 D) (Category.comp_id _) V) =
          (sectionsSquare (Opens.grothendieckTopology X) g (𝟙 D) (Category.comp_id _) U).comp
            (sectionsRestrictionSquare (Opens.grothendieckTopology X) h ι) := by
          simp only [CommAlgCat.AlgebraSquare.comp, sectionsRestrictionSquare, sectionsSquare]
          congr 1
          exact congrArg CommRingCat.Hom.hom (g.hom.naturality ι)
        have e' := congrArg (fun t => (CommAlgCat.cotangentComplexAbMap t).f n) e
        simp only [CommAlgCat.cotangentComplexAbMap_comp, HomologicalComplex.comp_f] at e'
        exact e' }
  comm' i j _ := by
    ext U : 2
    exact (CommAlgCat.cotangentComplexAbMap
      (sectionsSquare (Opens.grothendieckTopology X) g (𝟙 D) (Category.comp_id _) U)).comm i j

/-- The square of stalk maps `(A_x → D_x) ⟶ (B_x → D_x)` over `g_x` and the identity. -/
noncomputable def stalkChangeOfBaseSquare (x : X) :
    CommAlgCat.AlgebraSquare.{u, u, u} (stalkRing x A) (stalkRing x B)
      (stalkAlgebra (g ≫ h) x) (stalkAlgebra h x) :=
  letI : Algebra (stalkRing x A) (stalkRing x B) := (stalkMap g x).hom.toAlgebra
  letI : Algebra (stalkRing x B) (stalkRing x D) := (stalkMap h x).hom.toAlgebra
  letI : Algebra (stalkRing x A) (stalkRing x D) := (stalkMap (g ≫ h) x).hom.toAlgebra
  haveI : IsScalarTower (stalkRing x A) (stalkRing x B) (stalkRing x D) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map_comp g.hom h.hom))
  CommAlgCat.displaySquare₂ (stalkRing x A) (stalkRing x B) (stalkRing x D)

/-- At a point where `L_{B_x/A_x}` vanishes, the stalk map `L_{D_x/A_x} ⟶ L_{D_x/B_x}` is a
quasi-isomorphism. -/
theorem quasiIso_stalkChangeOfBaseSquare (x : X)
    (hg : IsZero (CommAlgCat.cotangentComplexDerived.{u, u} (stalkRing x A) (stalkAlgebra g x))) :
    QuasiIso (CommAlgCat.cotangentComplexAbMap (stalkChangeOfBaseSquare g h x)) :=
  let : Algebra (stalkRing x A) (stalkRing x B) := (stalkMap g x).hom.toAlgebra
  let : Algebra (stalkRing x B) (stalkRing x D) := (stalkMap h x).hom.toAlgebra
  let : Algebra (stalkRing x A) (stalkRing x D) := (stalkMap (g ≫ h) x).hom.toAlgebra
  have : IsScalarTower (stalkRing x A) (stalkRing x B) (stalkRing x D) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map_comp g.hom h.hom))
  CommAlgCat.quasiIso_cotangentComplexAbMap_displaySquare₂_of_isZero _ _ _ hg

/-- The stalk at `x` of the sectionwise change-of-base map is, through the comparisons with the
cotangent complexes of the stalks, the change-of-base map of the stalks. -/
theorem stalkCotangentComplex_comm (x : X) :
    ((TopCat.Presheaf.stalkAb x).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (sectionwiseChangeOfBase g h) ≫ stalkCotangentComplex h x =
      stalkCotangentComplex (g ≫ h) x ≫
        CommAlgCat.cotangentComplexAbMap (stalkChangeOfBaseSquare g h x) := by
  ext n : 1
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hU
  have h₁ := stalkCotangentTerm_germ h x n (OrderDual.toDual ⟨U, hU⟩)
  have h₂ := stalkCotangentTerm_germ (g ≫ h) x n (OrderDual.toDual ⟨U, hU⟩)
  have e : CommAlgCat.AlgebraSquare.comp.{u, u}
        (sectionsSquare (Opens.grothendieckTopology X) g (𝟙 D) (Category.comp_id _) (op U))
        (germSquare h x (OrderDual.toDual ⟨U, hU⟩)) =
      CommAlgCat.AlgebraSquare.comp.{u, u} (germSquare (g ≫ h) x (OrderDual.toDual ⟨U, hU⟩))
        (stalkChangeOfBaseSquare g h x) := by
    refine (CommAlgCat.AlgebraSquare.mk.injEq _ _ _ _ _ _).mpr ⟨?_, rfl⟩
    exact (congrArg CommRingCat.Hom.hom
      (TopCat.Presheaf.stalkFunctor_map_germ (nbhd (OrderDual.toDual ⟨U, hU⟩)) x hU g.hom)).symm
  have e' : (CommAlgCat.cotangentComplexAbMap
        (sectionsSquare (Opens.grothendieckTopology X) g (𝟙 D) (Category.comp_id _) (op U))).f n ≫
        (CommAlgCat.cotangentComplexAbMap (germSquare h x (OrderDual.toDual ⟨U, hU⟩))).f n =
      (CommAlgCat.cotangentComplexAbMap (germSquare (g ≫ h) x (OrderDual.toDual ⟨U, hU⟩))).f n ≫
        (CommAlgCat.cotangentComplexAbMap (stalkChangeOfBaseSquare g h x)).f n :=
    congrArg (fun φ => HomologicalComplex.Hom.f φ n)
      ((CommAlgCat.cotangentComplexAbMap_comp _ _).symm.trans
        ((congrArg CommAlgCat.cotangentComplexAbMap.{u, u, u} e).trans
          (CommAlgCat.cotangentComplexAbMap_comp _ _)))
  have h₀ := TopCat.Presheaf.stalkFunctor_map_germ U x hU ((sectionwiseChangeOfBase g h).f n)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ (stalkCotangentComplex h x).f n) h₀).trans
    ((Category.assoc _ _ _).trans
    ((congrArg (fun t => ((sectionwiseChangeOfBase g h).f n).app (op U) ≫ t) h₁).trans
    (e'.trans ((congrArg (fun t => t ≫ _) h₂.symm).trans (Category.assoc _ _ _))))))

/-- **The change-of-base map of a tower of sheaves of rings is checked on stalks.** Let
`A ⟶ B ⟶ D` be homomorphisms of sheaves of commutative rings on a topological space. If at every
point `x` the cotangent complex `L_{B_x/A_x}` of the map of stalks vanishes, then the canonical map
`L_{D/A} ⟶ L_{D/B}` is a quasi-isomorphism. -/
theorem quasiIso_towerCotangentChangeOfBase_of_isZero_stalk
    (hg : ∀ x : X,
      IsZero (CommAlgCat.cotangentComplexDerived.{u, u} (stalkRing x A) (stalkAlgebra g x))) :
    QuasiIso (towerCotangentChangeOfBase.{u, u, u} (Opens.grothendieckTopology X) g h) := by
  have hstalk : ∀ x : X, QuasiIso (((TopCat.Presheaf.stalkAb x).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (sectionwiseChangeOfBase g h)) := fun x => by
    have := quasiIso_stalkChangeOfBaseSquare g h x (hg x)
    exact (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk
      (@asIso _ _ _ _ (stalkCotangentComplex (g ≫ h) x) (isIso_stalkCotangentComplex (g ≫ h) x))
      (@asIso _ _ _ _ (stalkCotangentComplex h x) (isIso_stalkCotangentComplex h x))
      (stalkCotangentComplex_comm g h x).symm)).2 this
  have hW : ∀ n, (Opens.grothendieckTopology X).W
      (HomologicalComplex.homologyMap (sectionwiseChangeOfBase g h) n) := fun n =>
    TopCat.Presheaf.W_of_bijective_stalkFunctor_map _ fun x => by
      have h₁ : IsIso (HomologicalComplex.homologyMap
          (((TopCat.Presheaf.stalkAb x).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (sectionwiseChangeOfBase g h)) n) := by
        have := hstalk x
        infer_instance
      exact (ConcreteCategory.isIso_iff_bijective _).1
        ((isIso_map_homologyMap_iff _ (sectionwiseChangeOfBase g h) n).1 h₁)
  have hAb : QuasiIso (((SheafOfModules.toSheaf _).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (towerCotangentChangeOfBase.{u, u, u} (Opens.grothendieckTopology X) g h)) :=
    quasiIso_of_sectionwise_homology (Opens.grothendieckTopology X)
      (sectionwiseCotangentPresheafComplexComparison (Opens.grothendieckTopology X) (g ≫ h))
      (sectionwiseCotangentPresheafComplexComparison (Opens.grothendieckTopology X) h)
      (W_sectionwiseCotangentPresheafComplexComparison_f (Opens.grothendieckTopology X) (g ≫ h))
      (W_sectionwiseCotangentPresheafComplexComparison_f (Opens.grothendieckTopology X) h) _
      (sectionwiseChangeOfBase g h) (by
        refine HomologicalComplex.hom_ext _ _ fun n => NatTrans.ext (funext fun U => ?_)
        ext z
        exact (sectionsCotangentComplexComparison_square (Opens.grothendieckTopology X) g (𝟙 D)
          (Category.comp_id _) U n z).symm) hW
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (towerCotangentChangeOfBase.{u, u, u} (Opens.grothendieckTopology X) g h)
    (SheafOfModules.toSheaf _)).1 hAb

end Tower

end CategoryTheory.Sheaf
