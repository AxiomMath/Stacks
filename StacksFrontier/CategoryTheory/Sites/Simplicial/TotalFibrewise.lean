module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianSections

/-!
# Fibrewise restriction in the total site of a simplicial semi-representable object

Let `(C, J)` be a site and let `K` be a simplicial object of `SR(C)`. An object `T` of the total
site of `C/K` is a simplicial degree `n`, an index `i` and a chart `U ⟶ K_{n, i}`, and an arrow
`g : A ⟶ U` of `C` restricts it to the object of the same degree and index with the chart
`g ≫ (U ⟶ K_{n, i})`. This file constructs that restriction together with the morphism of the total
site it carries, and proves that every morphism of the total site is the Cartesian lift of its
simplicial degree followed by such a vertical morphism, and that a covering sieve of the object of
`C` underlying `T` pulls back to a covering sieve of the total topology.

## Main definitions

* `CategoryTheory.SimplicialSemiRepresentable.totalRestrict`: the fibrewise restriction of an
  object of the total site along an arrow of `C`.
* `CategoryTheory.SimplicialSemiRepresentable.totalVert`: the morphism of the total site from the
  fibrewise restriction of `T` along `g` to `T`; it lies over `g` and has identity simplicial
  degree.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable.totalHom_eq_ιNatTrans_comp_totalVert`: a morphism of
  the total site is the Cartesian lift of its simplicial degree followed by a vertical morphism.
* `CategoryTheory.SimplicialSemiRepresentable.exists_factor`: the same factorization, read as the
  existence of a factor whose image in `C` is invertible.
* `CategoryTheory.SimplicialSemiRepresentable.functorPullback_mem_totalTopology`: a covering sieve
  of the object of `C` underlying an object of the total site pulls back to a covering sieve of the
  total topology.

## Implementation notes

The source of a morphism of the fibre `∐ᵢ C/K_{n,i}` is *not* definitionally the fibrewise
restriction of its target along its image in `C`: that the two indices agree is recorded in the
constructor of `CategoryTheory.Sigma.SigmaHom`, and that the two charts agree is the commuting
triangle of an `Over`-morphism; both are propositional. Accordingly the factorization of a morphism
of the total site carries the `eqToHom` of
`CategoryTheory.SimplicialSemiRepresentable.slicesMap_obj_eq`, and for the same kind of reason
`totalVert_comp` carries the `eqToHom` of the associativity of `A'' ⟶ A' ⟶ A ⟶ K_{n, i}`.

## References

* [Stacks Project, Tag 09VU](https://stacks.math.columbia.edu/tag/09VU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory

/-- A functor sends the canonical morphism attached to an equality of objects, followed by an
arrow, to the canonical morphism attached to the induced equality, followed by the image of the
arrow. -/
theorem Functor.map_eqToHom_comp {D : Type*} [Category D] {E : Type*} [Category E] (F : D ⥤ E)
    {X Y Z : D} (h : X = Y) (f : Y ⟶ Z) (hF : F.obj X = F.obj Y) :
    F.map (eqToHom h ≫ f) = eqToHom hF ≫ F.map f := by
  subst h
  simp

namespace Sigma

variable {I : Type u} {D : I → Type u} [∀ i, SmallCategory (D i)]

/-- The canonical morphism attached to an equality of two objects of one component of a disjoint
union of categories, followed by an arrow of that component, is the image under the inclusion of
the component of the corresponding composite there. -/
theorem eqToHom_comp_mk {i : I} {X Y Z : D i} (h : X = Y) (f : Y ⟶ Z)
    (h' : (⟨i, X⟩ : Σ j, D j) = ⟨i, Y⟩) :
    eqToHom h' ≫ CategoryTheory.Sigma.SigmaHom.mk f =
      CategoryTheory.Sigma.SigmaHom.mk (eqToHom h ≫ f) := by
  subst h
  simp

end Sigma

namespace SemiRepresentable

variable {C : Type u} [SmallCategory C] {L : FormalCoproduct.{u} C}

/-- A morphism of `Over` out of a source identified by an equality is the canonical morphism
followed by a morphism with the same underlying arrow. -/
private theorem over_hom_eq_eqToHom_comp {X : C} {A A' B : Over X} (h : A = A') (f : A ⟶ B)
    (f' : A' ⟶ B) (hf : f.left = eqToHom (congrArg Over.left h) ≫ f'.left) :
    f = eqToHom h ≫ f' := by
  subst h
  exact Over.OverMorphism.ext (by simpa using hf)

/-- The source of a morphism of `∐ᵢ C/Lᵢ` is the chart of its target precomposed with the image of
the morphism in `C`. -/
theorem componentOver_src_eq {S T : ComponentOver L} (f : S ⟶ T) :
    S = ⟨T.1, Over.mk ((componentOverForget L).map f ≫ T.2.hom)⟩ := by
  cases f with
  | @mk i X Y g =>
    exact (congrArg (fun z : X.left ⟶ L.obj i => (⟨i, Over.mk z⟩ : ComponentOver L))
      (Over.w g)).symm

/-- A morphism of `∐ᵢ C/Lᵢ` is the canonical morphism out of the chart of its target precomposed
with its image in `C`. -/
theorem componentOver_hom_eq' {S T : ComponentOver L} (f : S ⟶ T) :
    f = eqToHom (componentOver_src_eq f) ≫ CategoryTheory.Sigma.SigmaHom.mk
      (Over.homMk ((componentOverForget L).map f) rfl) := by
  cases f with
  | @mk i X Y g =>
    have hX : X = Over.mk (g.left ≫ Y.hom) :=
      (congrArg (fun z : X.left ⟶ L.obj i => (Over.mk z : Over (L.obj i))) (Over.w g)).symm
    have hg : g = eqToHom hX ≫
        (Over.homMk g.left rfl : (Over.mk (g.left ≫ Y.hom) : Over (L.obj i)) ⟶ Y) :=
      over_hom_eq_eqToHom_comp hX _ _ (by simp)
    exact (congrArg (CategoryTheory.Sigma.incl
        (C := fun j : L.I => Over (L.obj j)) i).map hg).trans
      (Sigma.eqToHom_comp_mk (D := fun j : L.I => Over (L.obj j)) hX
        (Over.homMk g.left rfl : (Over.mk (g.left ≫ Y.hom) : Over (L.obj i)) ⟶ Y)
        (componentOver_src_eq (CategoryTheory.Sigma.SigmaHom.mk g))).symm

/-- A morphism of `∐ᵢ C/Lᵢ` is the canonical morphism out of the chart of its target precomposed
with its image in `C`, stated for a named image and a named identification of the source. -/
theorem componentOver_hom_eq {S T : ComponentOver L} (f : S ⟶ T)
    {m : S.2.left ⟶ T.2.left} (hm : (componentOverForget L).map f = m)
    (h : S = ⟨T.1, Over.mk (m ≫ T.2.hom)⟩) :
    f = eqToHom h ≫ CategoryTheory.Sigma.SigmaHom.mk (Over.homMk m rfl) := by
  subst hm
  exact componentOver_hom_eq' f

end SemiRepresentable

namespace SimplicialSemiRepresentable

open SemiRepresentable SimplicialSiteSituation

variable {C : Type u} [SmallCategory C] (K : SimplicialObject (FormalCoproduct.{u} C))

/-! ### The fibrewise restriction of an object of the total site -/

/-- The object of the total site obtained from `T` by restricting its chart along `g`: same
simplicial degree, same index, and the chart of `T` precomposed with `g`. -/
def totalRestrict (T : Grothendieck (slices K)) {A : C} (g : A ⟶ (totalForget K).obj T) :
    Grothendieck (slices K) :=
  ⟨T.base, ⟨T.fiber.1, Over.mk (g ≫ T.fiber.2.hom)⟩⟩

/-- The fibrewise restriction has the simplicial degree of the object restricted. -/
@[simp]
theorem totalRestrict_base (T : Grothendieck (slices K)) {A : C}
    (g : A ⟶ (totalForget K).obj T) : (totalRestrict K T g).base = T.base :=
  rfl

/-- The fibrewise restriction has the index of the object restricted. -/
@[simp]
theorem totalRestrict_fiber_fst (T : Grothendieck (slices K)) {A : C}
    (g : A ⟶ (totalForget K).obj T) : (totalRestrict K T g).fiber.1 = T.fiber.1 :=
  rfl

/-- The object of `C` underlying the fibrewise restriction along `g : A ⟶ _` is `A`. -/
@[simp]
theorem totalForget_obj_totalRestrict (T : Grothendieck (slices K)) {A : C}
    (g : A ⟶ (totalForget K).obj T) : (totalForget K).obj (totalRestrict K T g) = A :=
  rfl

/-- The fibrewise restriction of a fibrewise restriction is the fibrewise restriction of the
composite. -/
theorem totalRestrict_totalRestrict (T : Grothendieck (slices K)) {A A' : C}
    (g : A ⟶ (totalForget K).obj T) (k : A' ⟶ A) :
    totalRestrict K (totalRestrict K T g) k = totalRestrict K T (k ≫ g) :=
  congrArg (fun z : A' ⟶ (K.obj T.base).obj T.fiber.1 =>
      (⟨T.base, ⟨T.fiber.1, Over.mk z⟩⟩ : Grothendieck (slices K)))
    (Category.assoc k g T.fiber.2.hom).symm

/-! ### The vertical morphism carried by a fibrewise restriction -/

/-- The morphism of the total site from the fibrewise restriction of `T` along `g` to `T`; it lies
over `g` and has identity simplicial degree. -/
def totalVert (T : Grothendieck (slices K)) {A : C} (g : A ⟶ (totalForget K).obj T) :
    totalRestrict K T g ⟶ T :=
  (Grothendieck.ι (slices K) T.base).map
    (CategoryTheory.Sigma.SigmaHom.mk
      (Over.homMk g rfl : Over.mk (g ≫ T.fiber.2.hom) ⟶ T.fiber.2))

/-- The vertical morphism of a fibrewise restriction has identity simplicial degree. -/
@[simp]
theorem totalVert_base (T : Grothendieck (slices K)) {A : C}
    (g : A ⟶ (totalForget K).obj T) : (totalVert K T g).base = 𝟙 T.base :=
  rfl

/-- The localization functor of the total site reads a morphism inside one simplicial degree as the
localization functor of that degree does. -/
theorem totalForget_map_ι_map {c : SimplexCategoryᵒᵖ} {X Y : (slices K).obj c} (f : X ⟶ Y) :
    (totalForget K).map ((Grothendieck.ι (slices K) c).map f) = (sliceForget K c).map f := by
  refine (totalForget_map K ((Grothendieck.ι (slices K) c).map f)).trans ?_
  exact ((sliceForget K c).map_eqToHom_comp
      (show ((slices K).map (𝟙 c)).toFunctor.obj X = X by simp) f rfl).trans
    (Category.id_comp ((sliceForget K c).map f))

/-- The vertical morphism of the fibrewise restriction along `g` lies over `g`. -/
@[simp]
theorem totalForget_map_totalVert (T : Grothendieck (slices K)) {A : C}
    (g : A ⟶ (totalForget K).obj T) : (totalForget K).map (totalVert K T g) = g :=
  totalForget_map_ι_map K (CategoryTheory.Sigma.SigmaHom.mk
    (Over.homMk g rfl : Over.mk (g ≫ T.fiber.2.hom) ⟶ T.fiber.2))

/-- Restricting along `g` and then along `k` is restricting along `k ≫ g`. -/
theorem totalVert_comp (T : Grothendieck (slices K)) {A A' : C}
    (g : A ⟶ (totalForget K).obj T) (k : A' ⟶ A) :
    totalVert K (totalRestrict K T g) k ≫ totalVert K T g =
      eqToHom (totalRestrict_totalRestrict K T g k) ≫ totalVert K T (k ≫ g) := by
  have hX : (Over.mk (k ≫ g ≫ T.fiber.2.hom) : Over ((K.obj T.base).obj T.fiber.1)) =
      Over.mk ((k ≫ g) ≫ T.fiber.2.hom) :=
    congrArg (fun z : A' ⟶ (K.obj T.base).obj T.fiber.1 =>
        (Over.mk z : Over ((K.obj T.base).obj T.fiber.1)))
      (Category.assoc k g T.fiber.2.hom).symm
  have hover :
      (Over.homMk k rfl : Over.mk (k ≫ g ≫ T.fiber.2.hom) ⟶ Over.mk (g ≫ T.fiber.2.hom)) ≫
          (Over.homMk g rfl : Over.mk (g ≫ T.fiber.2.hom) ⟶ T.fiber.2) =
        eqToHom hX ≫
          (Over.homMk (k ≫ g) rfl : Over.mk ((k ≫ g) ≫ T.fiber.2.hom) ⟶ T.fiber.2) :=
    over_hom_eq_eqToHom_comp hX _ _ (by simp; rfl)
  let F := CategoryTheory.Sigma.incl
      (C := fun j : (K.obj T.base).I => Over ((K.obj T.base).obj j)) T.fiber.1 ⋙
    Grothendieck.ι (slices K) T.base
  exact (F.map_comp _ _).symm.trans <| (congrArg F.map hover).trans <|
    F.map_eqToHom_comp hX _ (totalRestrict_totalRestrict K T g k)

/-! ### Every morphism of the total site is a Cartesian lift followed by a vertical morphism -/

/-- The restriction of the chart of `W` along the simplicial degree of a morphism `θ : W ⟶ T` is
the fibrewise restriction of the chart of `T` along the image of `θ` in `C`. -/
theorem slicesMap_obj_eq {W T : Grothendieck (slices K)} (θ : W ⟶ T) :
    ((slices K).map θ.base).toFunctor.obj W.fiber =
      ⟨T.fiber.1, Over.mk ((totalForget K).map θ ≫ T.fiber.2.hom)⟩ :=
  (componentOver_src_eq θ.fiber).trans
    (congrArg (fun z : (totalForget K).obj W ⟶ (totalForget K).obj T =>
        (⟨T.fiber.1, Over.mk (z ≫ T.fiber.2.hom)⟩ : ComponentOver (K.obj T.base)))
      (totalForget_map K θ).symm)

/-- The target of the Cartesian lift of the simplicial degree of a morphism `θ : W ⟶ T` of the
total site is the fibrewise restriction of `T` along the image of `θ` in `C`. -/
theorem ι_obj_slicesMap_obj_eq {W T : Grothendieck (slices K)} (θ : W ⟶ T) :
    (Grothendieck.ι (slices K) T.base).obj (((slices K).map θ.base).toFunctor.obj W.fiber) =
      totalRestrict K T ((totalForget K).map θ) :=
  congrArg (Grothendieck.ι (slices K) T.base).obj (slicesMap_obj_eq K θ)

/-- **A morphism of the total site factors through a fibrewise restriction.** It is the Cartesian
lift of its simplicial degree followed by the vertical morphism over its image in `C`. -/
theorem totalHom_eq_ιNatTrans_comp_totalVert {W T : Grothendieck (slices K)} (θ : W ⟶ T) :
    θ = (Grothendieck.ιNatTrans (F := slices K) θ.base).app W.fiber ≫
      eqToHom (ι_obj_slicesMap_obj_eq K θ) ≫ totalVert K T ((totalForget K).map θ) := by
  have hmap : (Grothendieck.ι (slices K) T.base).map (eqToHom (slicesMap_obj_eq K θ)) =
      eqToHom (ι_obj_slicesMap_obj_eq K θ) :=
    eqToHom_map (Grothendieck.ι (slices K) T.base) (slicesMap_obj_eq K θ)
  refine (Grothendieck.ιNatTrans_app_comp_ι_map θ.base θ.fiber).symm.trans ?_
  refine congrArg (fun z => (Grothendieck.ιNatTrans (F := slices K) θ.base).app W.fiber ≫ z) ?_
  refine (congrArg (Grothendieck.ι (slices K) T.base).map
    (componentOver_hom_eq θ.fiber (totalForget_map K θ).symm (slicesMap_obj_eq K θ))).trans ?_
  refine (Functor.map_comp _ _ _).trans ?_
  exact congrArg (fun z => z ≫ totalVert K T ((totalForget K).map θ)) hmap

/-- The image in `C` of the Cartesian lift of a simplex map is an identity. -/
theorem totalForget_map_ιNatTrans_app {c c' : SimplexCategoryᵒᵖ} (b : c ⟶ c')
    (d : (slices K).obj c) :
    (totalForget K).map ((Grothendieck.ιNatTrans (F := slices K) b).app d) =
      𝟙 ((sliceForget K c).obj d) :=
  (totalForget_map K ((Grothendieck.ιNatTrans (F := slices K) b).app d)).trans
    (Functor.map_id (sliceForget K c') (((slices K).map b).toFunctor.obj d))

/-- **A morphism of the total site is a Cartesian lift followed by a vertical morphism.** The
Cartesian factor is the lift of the simplicial degree of the morphism, so its image in `C` is the
identity, and the vertical factor lies over the image of the morphism in `C`. -/
theorem exists_factor {W T : Grothendieck (slices K)} (θ : W ⟶ T) :
    ∃ ρ : W ⟶ totalRestrict K T ((totalForget K).map θ),
      (totalForget K).map ρ = 𝟙 _ ∧ ρ ≫ totalVert K T ((totalForget K).map θ) = θ := by
  refine ⟨(Grothendieck.ιNatTrans (F := slices K) θ.base).app W.fiber ≫
    eqToHom (ι_obj_slicesMap_obj_eq K θ), ?_, ?_⟩
  · have hcomp : (totalForget K).map
          ((Grothendieck.ιNatTrans (F := slices K) θ.base).app W.fiber ≫
            eqToHom (ι_obj_slicesMap_obj_eq K θ)) =
        (totalForget K).map ((Grothendieck.ιNatTrans (F := slices K) θ.base).app W.fiber) ≫
          (totalForget K).map (eqToHom (ι_obj_slicesMap_obj_eq K θ)) :=
      Functor.map_comp (totalForget K)
        ((Grothendieck.ιNatTrans (F := slices K) θ.base).app W.fiber)
        (eqToHom (ι_obj_slicesMap_obj_eq K θ))
    refine hcomp.trans ?_
    refine Eq.trans (congrArg₂ (fun a b => a ≫ b)
      (totalForget_map_ιNatTrans_app K θ.base W.fiber)
      ((eqToHom_map (totalForget K) (ι_obj_slicesMap_obj_eq K θ)).trans
        (eqToHom_refl _ _))) ?_
    exact Category.id_comp _
  · exact (Category.assoc _ _ _).trans (totalHom_eq_ιNatTrans_comp_totalVert K θ).symm

/-! ### Covering sieves of the underlying object of `C` -/

/-- A covering sieve of the object of `C` underlying an object of the total site pulls back to a
covering sieve of the total topology. -/
theorem functorPullback_mem_totalTopology (J : GrothendieckTopology C)
    [J.toCoverage.HasPullbacks] (T : Grothendieck (slices K))
    (S : Sieve ((totalForget K).obj T)) (hS : S ∈ J ((totalForget K).obj T)) :
    Sieve.functorPullback (totalForget K) S ∈ (situation J K).totalTopology T :=
  (totalForget K).cover_lift ((situation J K).totalTopology) J hS

end SimplicialSemiRepresentable

end CategoryTheory

end
