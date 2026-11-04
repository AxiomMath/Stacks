module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Copower

/-!
# The copower of an abelian presheaf by a presheaf of sets, and sheafification

Let `(C, J)` be a small site, let `G : Cᵒᵖ ⥤ Type u` be a presheaf of sets and let
`P : Cᵒᵖ ⥤ AddCommGrpCat.{u}` be an abelian presheaf. The copower
`P.copower G : V ↦ ∐_{s ∈ G(V)} P(V)` of `CategoryTheory.Functor.copower` is then again an
abelian presheaf, functorially in `P`. This file records the two properties of that construction
which the proof of [Stacks, Tag 09D2] uses:

* it is an exact functor of `P`, so it preserves homology, and
* it does not see the difference between an abelian presheaf and its sheafification: if `P`
  sheafifies to zero then so does `P.copower G`.

The second statement is the local one. A presheaf of abelian groups sheafifies to zero exactly
when every one of its sections is killed by restriction along the arrows of some covering sieve,
and a section of `P.copower G` over `V` is a finite sum of sections of `P(V)` placed in the
summands indexed by the elements of `G(V)`; each summand dies on a covering sieve, and finitely
many covering sieves have a covering intersection.

## Main definitions

* `Stacks.abCopowerFunctor`: the copower endofunctor `M ↦ ∐_{s ∈ S} M` of abelian groups for a
  fixed index set `S`, realised as `Functor.const (Discrete S) ⋙ colim` so that its exactness is
  Grothendieck's axiom AB4 for abelian groups.
* `Stacks.copowerFunctor`: the functor `P ↦ P.copower G` on abelian presheaves.
* `Stacks.locallyZero`: the subgroup of those sections of an abelian presheaf over an object
  which are killed by restriction along the arrows of some covering sieve.

## Main results

* `Stacks.copowerFunctor_preservesFiniteLimits`,
  `Stacks.copowerFunctor_preservesFiniteColimits`,
  `Stacks.copowerFunctor_preservesHomology`: the copower functor is exact, hence preserves
  homology. Exactness is checked after evaluation at each object of the site, where the functor
  becomes the copower endofunctor of abelian groups at a fixed set.
* `Stacks.isZero_presheafToSheaf_copower`: if `P` sheafifies to zero then so does `P.copower G`.
* `Stacks.w_copowerFunctor_map`: if sheafification inverts a morphism of abelian presheaves then
  it inverts its copower; this is the previous item applied to the kernel and the cokernel.
* `Stacks.quasiIso_mapHomologicalComplex_presheafToSheaf_copowerFunctor`: the same implication
  for a morphism of cochain complexes of abelian presheaves and quasi-isomorphisms.

## References

* [Stacks, Tag 09D2](https://stacks.math.columbia.edu/tag/09D2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite ZeroObject

universe u

namespace Stacks

/-! ### The copower of an abelian group by a fixed set -/

section AbCopower

variable (S : Type u)

/-- The copower endofunctor `M ↦ ∐_{s ∈ S} M` of abelian groups, for a fixed index set `S`,
written as the composite of the constant-diagram functor on the discrete category `S` with the
colimit functor. In that form its exactness is the statement that `S`-indexed coproducts of
abelian groups are exact, which is Grothendieck's axiom AB4. -/
def abCopowerFunctor : AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  Functor.const (Discrete S) ⋙ colim

/-- `Stacks.abCopowerFunctor` preserves finite limits: the constant-diagram functor is a right
adjoint, and `colim` over a discrete category is left exact by AB4 for abelian groups. -/
instance abCopowerFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (abCopowerFunctor S) := by
  have _h₁ : PreservesLimitsOfSize.{0, 0}
      (Functor.const (Discrete S) : AddCommGrpCat.{u} ⥤ Discrete S ⥤ AddCommGrpCat.{u}) :=
    colimConstAdj.rightAdjoint_preservesLimits
  have _h₂ : PreservesFiniteLimits
      (Functor.const (Discrete S) : AddCommGrpCat.{u} ⥤ Discrete S ⥤ AddCommGrpCat.{u}) :=
    PreservesLimitsOfSize.preservesFiniteLimits _
  have _h₃ : PreservesFiniteLimits
      (colim : (Discrete S ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}) :=
    HasExactColimitsOfShape.preservesFiniteLimits
  exact comp_preservesFiniteLimits _ _

/-- `Stacks.abCopowerFunctor` preserves finite colimits: both factors are left adjoints. -/
instance abCopowerFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (abCopowerFunctor S) := by
  have _h₁ : PreservesColimitsOfSize.{0, 0}
      (Functor.const (Discrete S) : AddCommGrpCat.{u} ⥤ Discrete S ⥤ AddCommGrpCat.{u}) :=
    constLimAdj.leftAdjoint_preservesColimits
  have _h₂ : PreservesFiniteColimits
      (Functor.const (Discrete S) : AddCommGrpCat.{u} ⥤ Discrete S ⥤ AddCommGrpCat.{u}) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  have _h₃ : PreservesColimitsOfSize.{0, 0}
      (colim : (Discrete S ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}) :=
    colimConstAdj.leftAdjoint_preservesColimits
  have _h₄ : PreservesFiniteColimits
      (colim : (Discrete S ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  exact comp_preservesFiniteColimits _ _

/-- **The summand inclusions of a copower of abelian groups generate it**: a subgroup of
`∐_{s ∈ S} M` which contains the image of every summand inclusion is the whole group.

The inclusions factor through such a subgroup, so the universal property of the coproduct
produces a retraction of its inclusion, which is therefore surjective. -/
lemma eq_top_of_sigmaIota_mem {M : AddCommGrpCat.{u}}
    (Z : AddSubgroup (ToType (∐ fun _ : S => M)))
    (h : ∀ (s : S) (m : ToType M), Sigma.ι (fun _ : S => M) s m ∈ Z) : Z = ⊤ := by
  refine (AddSubgroup.eq_top_iff' Z).2 fun y => ?_
  let e : (∐ fun _ : S => M) ⟶ AddCommGrpCat.of Z :=
    Sigma.desc fun s => AddCommGrpCat.ofHom
      ((ConcreteCategory.hom (Sigma.ι (fun _ : S => M) s)).codRestrict Z (h s))
  have hsplit : e ≫ AddCommGrpCat.ofHom Z.subtype = 𝟙 (∐ fun _ : S => M) := by
    refine Sigma.hom_ext _ _ fun s => ?_
    refine ConcreteCategory.hom_ext _ _ fun m => ?_
    simp [e]
  have hy := ConcreteCategory.congr_hom hsplit y
  simp only [CategoryTheory.comp_apply, CategoryTheory.id_apply] at hy
  exact hy ▸ (e y).2

end AbCopower

/-! ### The copower of an abelian presheaf by a presheaf of sets -/

section CopowerFunctor

variable {C : Type u} [SmallCategory C]

/-- The functor `P ↦ P.copower G` sending an abelian presheaf to its copower by a fixed presheaf
of sets `G`, i.e. to `V ↦ ∐_{s ∈ G(V)} P(V)`, and a morphism `b` to `Functor.copowerMap b (𝟙 G)`,
which carries the summand indexed by `s` to the summand indexed by `s` by `b`. -/
def copowerFunctor (G : Cᵒᵖ ⥤ Type u) :
    (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u}) where
  obj P := P.copower G
  map b := Functor.copowerMap b (𝟙 G)
  map_id P := Functor.copowerMap_id P G
  map_comp b b' := by simp

/-- Evaluating `Stacks.copowerFunctor G` at an object `V` of the site is evaluation at `V`
followed by the copower endofunctor of abelian groups at the set `G(V)`: both send `P` to
`∐_{s ∈ G(V)} P(V)`, and both send `b` to the morphism acting as `b_V` on each summand. -/
def copowerFunctorCompEvaluationIso (G : Cᵒᵖ ⥤ Type u) (V : Cᵒᵖ) :
    copowerFunctor G ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj V ≅
      (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj V ⋙ abCopowerFunctor (G.obj V) :=
  NatIso.ofComponents
    (fun P => (HasColimit.isoOfNatIso (Discrete.natIso fun _ => Iso.refl (P.obj V)) :
      (∐ fun _ : G.obj V => P.obj V) ≅
        colimit ((Functor.const (Discrete (G.obj V))).obj (P.obj V))))
    (fun {P Q} b => by
      refine Sigma.hom_ext _ _ fun s => ?_
      simp [copowerFunctor, abCopowerFunctor, HasColimit.isoOfNatIso_ι_hom])

/-- `Stacks.copowerFunctor` preserves finite limits: limits of presheaves are computed objectwise,
and after evaluation the functor becomes the copower endofunctor of abelian groups at a fixed
set, which is left exact. -/
instance copowerFunctor_preservesFiniteLimits (G : Cᵒᵖ ⥤ Type u) :
    PreservesFiniteLimits (copowerFunctor G) :=
  preservesFiniteLimits_of_evaluation _ fun V =>
    preservesFiniteLimits_of_natIso (copowerFunctorCompEvaluationIso G V).symm

/-- `Stacks.copowerFunctor` preserves finite colimits, by the same objectwise reduction. -/
instance copowerFunctor_preservesFiniteColimits (G : Cᵒᵖ ⥤ Type u) :
    PreservesFiniteColimits (copowerFunctor G) :=
  preservesFiniteColimits_of_evaluation _ fun V =>
    preservesFiniteColimits_of_natIso (copowerFunctorCompEvaluationIso G V).symm

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts in
/-- `Stacks.copowerFunctor` is additive, preserving binary products between additive
categories. -/
instance copowerFunctor_additive (G : Cᵒᵖ ⥤ Type u) : (copowerFunctor G).Additive :=
  (copowerFunctor G).additive_of_preservesBinaryBiproducts

/-- `Stacks.copowerFunctor` preserves homology, being an exact functor between abelian
categories. -/
instance copowerFunctor_preservesHomology (G : Cᵒᵖ ⥤ Type u) :
    (copowerFunctor G).PreservesHomology :=
  Functor.preservesHomologyOfExact _

end CopowerFunctor

/-! ### Sections which vanish locally -/

section LocallyZero

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- The subgroup of those sections of an abelian presheaf `P` over an object `X` which are killed
by restriction along every arrow of some covering sieve of `X`. -/
def locallyZero (P : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (X : Cᵒᵖ) : AddSubgroup (ToType (P.obj X)) where
  carrier := {x | Presheaf.equalizerSieve (F := P) x 0 ∈ J X.unop}
  zero_mem' := by simp
  add_mem' {x y} hx hy := by
    refine J.superset_covering ?_ (J.intersection_covering hx hy)
    rintro Y f ⟨hfx, hfy⟩
    simp only [Presheaf.equalizerSieve_apply, map_zero] at hfx hfy ⊢
    rw [map_add, hfx, hfy, add_zero]
  neg_mem' {x} hx := by
    refine J.superset_covering ?_ hx
    intro Y f hf
    simp only [Presheaf.equalizerSieve_apply, map_zero] at hf ⊢
    rw [map_neg, hf, neg_zero]

/-- **A section of an abelian presheaf which sheafifies to zero dies on a covering sieve.**

The unit of sheafification is locally injective, and the section and zero have the same -- namely
the only -- image in the zero group of sections of the sheafification. -/
theorem mem_locallyZero_of_isZero_presheafToSheaf (P : Cᵒᵖ ⥤ AddCommGrpCat.{u})
    (hP : IsZero ((presheafToSheaf J AddCommGrpCat.{u}).obj P)) (X : Cᵒᵖ)
    (x : ToType (P.obj X)) : x ∈ locallyZero J P X := by
  have hz : IsZero ((sheafify J P).obj X) :=
    (sheafToPresheaf J AddCommGrpCat.{u} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj X).map_isZero hP
  have hsub : Subsingleton (ToType ((sheafify J P).obj X)) :=
    AddCommGrpCat.isZero_iff_subsingleton.mp hz
  exact Presheaf.equalizerSieve_mem J (toSheafify J P) x 0 (hsub.allEq _ _)

/-- **An abelian presheaf all of whose sections die on a covering sieve sheafifies to zero.**

Such a presheaf has a locally bijective -- locally injective because two sections differ by one
which vanishes locally, locally surjective for free -- map to the zero presheaf, and
sheafification inverts the locally bijective maps. -/
theorem isZero_presheafToSheaf_of_mem_locallyZero (P : Cᵒᵖ ⥤ AddCommGrpCat.{u})
    (hP : ∀ (X : Cᵒᵖ) (x : ToType (P.obj X)), x ∈ locallyZero J P X) :
    IsZero ((presheafToSheaf J AddCommGrpCat.{u}).obj P) := by
  have _hli : Presheaf.IsLocallyInjective J (0 : P ⟶ (0 : Cᵒᵖ ⥤ AddCommGrpCat.{u})) := by
    refine ⟨fun {X} x y _ => ?_⟩
    refine J.superset_covering ?_ ((locallyZero J P X).sub_mem (hP X x) (hP X y))
    intro Y f hf
    simpa only [Presheaf.equalizerSieve_apply, map_zero, map_sub, sub_eq_zero] using hf
  have hzero : ∀ X : Cᵒᵖ, Subsingleton (ToType ((0 : Cᵒᵖ ⥤ AddCommGrpCat.{u}).obj X)) := fun X =>
    AddCommGrpCat.isZero_iff_subsingleton.mp
      (((evaluation Cᵒᵖ AddCommGrpCat.{u}).obj X).map_isZero (isZero_zero _))
  have _hls : Presheaf.IsLocallySurjective J (0 : P ⟶ (0 : Cᵒᵖ ⥤ AddCommGrpCat.{u})) :=
    Presheaf.isLocallySurjective_of_surjective J _ fun X _ => ⟨0, (hzero X).allEq _ _⟩
  have _hiso : IsIso ((presheafToSheaf J AddCommGrpCat.{u}).map
      (0 : P ⟶ (0 : Cᵒᵖ ⥤ AddCommGrpCat.{u}))) :=
    (J.W_iff _).mp (J.W_of_isLocallyBijective _)
  exact ((presheafToSheaf J AddCommGrpCat.{u}).map_isZero
    (isZero_zero (Cᵒᵖ ⥤ AddCommGrpCat.{u}))).of_iso
    (asIso ((presheafToSheaf J AddCommGrpCat.{u}).map
      (0 : P ⟶ (0 : Cᵒᵖ ⥤ AddCommGrpCat.{u}))))

/-- **An abelian presheaf which sheafifies to zero has a copower which sheafifies to zero.**

A section of `P.copower G` over `X` lies in the subgroup of locally vanishing sections as soon as
every section of the form `ι_s m` does, by `Stacks.eq_top_of_sigmaIota_mem`; and `ι_s m` dies on
any covering sieve on which `m` dies, because the restriction maps of the copower carry the
summand indexed by `s` into a summand by the restriction maps of `P`. -/
theorem isZero_presheafToSheaf_copower (G : Cᵒᵖ ⥤ Type u) {P : Cᵒᵖ ⥤ AddCommGrpCat.{u}}
    (hP : IsZero ((presheafToSheaf J AddCommGrpCat.{u}).obj P)) :
    IsZero ((presheafToSheaf J AddCommGrpCat.{u}).obj (P.copower G)) := by
  refine isZero_presheafToSheaf_of_mem_locallyZero J _ fun X x => ?_
  have htop : locallyZero J (P.copower G) X = ⊤ := by
    refine eq_top_of_sigmaIota_mem _ _ fun s m => ?_
    refine J.superset_covering ?_ (mem_locallyZero_of_isZero_presheafToSheaf J P hP X m)
    intro Y f hf
    simp only [Presheaf.equalizerSieve_apply, map_zero, Functor.copower_map] at hf ⊢
    have hc := ConcreteCategory.congr_hom
      (Sigma.ι_comp_map' (g := fun _ => P.obj _) (G.map f.op) (fun _ => P.map f.op) s) m
    simp only [CategoryTheory.comp_apply] at hc
    rw [hc, hf, map_zero]
  simp [htop]

end LocallyZero

/-! ### Homology of a complex after an exact functor -/

section HomologyTransfer

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B] (F : A ⥤ B)
  [F.Additive] [F.PreservesHomology] {S₁ S₂ : ShortComplex A} (φ : S₁ ⟶ S₂)

/-- For an additive functor preserving homology, the map it induces on the homology of the image
of a short complex is the functor applied to the homology map, conjugated by
`CategoryTheory.ShortComplex.mapHomologyIso`. -/
lemma homologyMap_mapShortComplex_map :
    ShortComplex.homologyMap (F.mapShortComplex.map φ) =
      (S₁.mapHomologyIso F).hom ≫ F.map (ShortComplex.homologyMap φ) ≫
        (S₂.mapHomologyIso F).inv := by
  rw [← Category.assoc, Iso.eq_comp_inv]
  exact ShortComplex.mapHomologyIso_hom_naturality φ F

/-- The form of `Stacks.homologyMap_mapShortComplex_map` solved for the functor applied to the
homology map. -/
lemma map_homologyMap :
    F.map (ShortComplex.homologyMap φ) =
      (S₁.mapHomologyIso F).inv ≫ ShortComplex.homologyMap (F.mapShortComplex.map φ) ≫
        (S₂.mapHomologyIso F).hom := by
  rw [homologyMap_mapShortComplex_map]
  simp

end HomologyTransfer

/-! ### Sheafification does not see the copower -/

section Transfer

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- **Sheafification inverts the copower of a morphism it inverts.**

The copower functor is exact, so it carries the kernel and the cokernel of `g` to the kernel and
the cokernel of its copower; sheafification is exact too, so it carries them to the kernel and
the cokernel of the sheafified morphism. Those vanish because `g` is inverted, hence so do the
sheafifications of the copowers by `Stacks.isZero_presheafToSheaf_copower`, and a morphism of an
abelian category with vanishing kernel and cokernel is an isomorphism. -/
theorem w_copowerFunctor_map (G : Cᵒᵖ ⥤ Type u) {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (g : P ⟶ Q)
    (hg : J.W g) : J.W ((copowerFunctor G).map g) := by
  have _hiso : IsIso ((presheafToSheaf J AddCommGrpCat.{u}).map g) := (J.W_iff _).mp hg
  have hker : IsZero ((presheafToSheaf J AddCommGrpCat.{u}).obj (kernel g)) :=
    (isZero_kernel_of_mono ((presheafToSheaf J AddCommGrpCat.{u}).map g)).of_iso
      (PreservesKernel.iso (presheafToSheaf J AddCommGrpCat.{u}) g)
  have hcoker : IsZero ((presheafToSheaf J AddCommGrpCat.{u}).obj (cokernel g)) :=
    (isZero_cokernel_of_epi ((presheafToSheaf J AddCommGrpCat.{u}).map g)).of_iso
      (PreservesCokernel.iso (presheafToSheaf J AddCommGrpCat.{u}) g)
  have hker' : IsZero ((presheafToSheaf J AddCommGrpCat.{u}).obj
      (kernel ((copowerFunctor G).map g))) :=
    ((isZero_presheafToSheaf_copower J G hker).of_iso
      ((presheafToSheaf J AddCommGrpCat.{u}).mapIso
        (PreservesKernel.iso (copowerFunctor G) g).symm))
  have hcoker' : IsZero ((presheafToSheaf J AddCommGrpCat.{u}).obj
      (cokernel ((copowerFunctor G).map g))) :=
    ((isZero_presheafToSheaf_copower J G hcoker).of_iso
      ((presheafToSheaf J AddCommGrpCat.{u}).mapIso
        (PreservesCokernel.iso (copowerFunctor G) g).symm))
  have hmono : Mono ((presheafToSheaf J AddCommGrpCat.{u}).map ((copowerFunctor G).map g)) :=
    Preadditive.mono_of_isZero_kernel _ (hker'.of_iso
      (PreservesKernel.iso (presheafToSheaf J AddCommGrpCat.{u})
        ((copowerFunctor G).map g)).symm)
  have hepi : Epi ((presheafToSheaf J AddCommGrpCat.{u}).map ((copowerFunctor G).map g)) :=
    Preadditive.epi_of_isZero_cokernel _ (hcoker'.of_iso
      (PreservesCokernel.iso (presheafToSheaf J AddCommGrpCat.{u})
        ((copowerFunctor G).map g)).symm)
  exact (J.W_iff _).mpr ((isIso_iff_mono_and_epi _).mpr ⟨hmono, hepi⟩)

/-- **Sheafification does not see the difference between a morphism of cochain complexes of
abelian presheaves and its copower.** If the sheafification of `f` is a quasi-isomorphism, then
so is the sheafification of the copower of `f` by any presheaf of sets `G`.

Both the copower functor and sheafification preserve homology, so in each degree the homology
map of the sheafified copower is, up to isomorphism, sheafification applied to the copower of the
homology map of `f`; sheafification inverts the latter by `Stacks.w_copowerFunctor_map`. -/
theorem quasiIso_mapHomologicalComplex_presheafToSheaf_copowerFunctor (G : Cᵒᵖ ⥤ Type u)
    {K L : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ} (f : K ⟶ L)
    (hf : QuasiIso (((presheafToSheaf J AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f)) :
    QuasiIso (((presheafToSheaf J AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (((copowerFunctor G).mapHomologicalComplex (ComplexShape.up ℤ)).map f)) := by
  refine ⟨fun n => ?_⟩
  have h1 := hf.quasiIsoAt n
  rw [quasiIsoAt_iff, ShortComplex.quasiIso_iff] at h1
  rw [quasiIsoAt_iff, ShortComplex.quasiIso_iff]
  have _h2 : IsIso (ShortComplex.homologyMap
      ((presheafToSheaf J AddCommGrpCat.{u}).mapShortComplex.map
        ((HomologicalComplex.shortComplexFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{u})
          (ComplexShape.up ℤ) n).map f))) := h1
  have h3 : IsIso ((presheafToSheaf J AddCommGrpCat.{u}).map (ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{u})
        (ComplexShape.up ℤ) n).map f))) := by
    rw [map_homologyMap]
    infer_instance
  have _h4 : IsIso ((presheafToSheaf J AddCommGrpCat.{u}).map ((copowerFunctor G).map
      (ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{u})
          (ComplexShape.up ℤ) n).map f)))) :=
    (J.W_iff _).mp (w_copowerFunctor_map J G _ ((J.W_iff _).mpr h3))
  have h5 : IsIso (ShortComplex.homologyMap
      ((presheafToSheaf J AddCommGrpCat.{u}).mapShortComplex.map
        ((copowerFunctor G).mapShortComplex.map
          ((HomologicalComplex.shortComplexFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{u})
            (ComplexShape.up ℤ) n).map f)))) := by
    rw [homologyMap_mapShortComplex_map, homologyMap_mapShortComplex_map, Functor.map_comp,
      Functor.map_comp]
    infer_instance
  exact h5

end Transfer

end Stacks

end
