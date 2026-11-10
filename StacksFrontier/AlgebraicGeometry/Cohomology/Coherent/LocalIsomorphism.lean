module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.ProperMapping.CoherenceClosure
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.LocalSurjectivity
import all StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.LocalSurjectivity

/-!
# Local injectivity for morphisms into a coherent module

Let `R` be a sheaf of rings on a topological space `X` and let `φ : G ⟶ F` be a morphism of
`R`-modules with `G` of finite type and `F` coherent. If `φ` is injective on the stalk at a
point `x`, then its restriction to some open neighbourhood of `x` is a monomorphism.

## Main results

* `AlgebraicGeometry.exists_isMono_over_of_stalk_injective`: injectivity on one stalk gives a
  monomorphism after restriction to a neighbourhood. This is Tag 01C0, which Tag 01Y3 part (2)
  cites.

## Implementation notes

The kernel `K` of `φ` is of finite type, because `G` is of finite type and `F` is coherent; this
is the source's coherence closure lemma. Injectivity of `φ` on the stalk at `x` forces the stalk
of `K` at `x` to vanish: the inclusion `K ⟶ G` is a monomorphism, hence injective on sections and
therefore on stalks, so a germ of `K` at `x` whose image in `G` is killed by `φ` already vanishes.
A finite type module with vanishing stalk at `x` vanishes on a neighbourhood of `x`, and a kernel
is computed before or after restriction indifferently, so `φ` restricted to that neighbourhood has
zero kernel and is a monomorphism.

Neither `Epi` nor `IsZero` of a restriction is phrased in a way that survives passing to a
smaller open — the restricted morphism lives in a different category for each open. The monotone
invariant is the section-level local surjectivity
`Stacks.SheafOfModules.LocallySurjective.LocallySurjOn` of Tag 01B8, which is a condition at the
points of its open set and therefore inherited by subsets, and vanishing of the kernel is read
off it through the zero endomorphism of the kernel.

## References

* [Stacks Project, Tag 01Y3](https://stacks.math.columbia.edu/tag/01Y3)
* [Stacks Project, Tag 01C0](https://stacks.math.columbia.edu/tag/01C0)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : TopCat.{u}}
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}

/-- A module whose zero endomorphism is locally surjective over `W` vanishes after restriction
to `W`: the zero morphism of the restriction is an epimorphism, which forces the identity of the
restriction to be zero. -/
private lemma isZero_over_of_locallySurjOn_zero (K : SheafOfModules.{u} R) (W : Opens X)
    (h : Stacks.SheafOfModules.LocallySurjective.LocallySurjOn (X := auxiliaryRingedSpace X) (0 : K
      ⟶ K) W) :
    IsZero (K.over W) := by
  have h0 : ((0 : K ⟶ K).over W) = (0 : K.over W ⟶ K.over W) := by
    change (SheafOfModules.overFunctor R W).map (0 : K ⟶ K) = 0
    rfl
  have hepi : Epi ((0 : K ⟶ K).over W) :=
    epi_over_of_locallySurjOn (Y := auxiliaryRingedSpace X) (0 : K ⟶ K) W h
  rw [h0] at hepi
  exact (IsZero.iff_id_eq_zero _).2
    ((cancel_epi (0 : K.over W ⟶ K.over W)).1 (by simp))

/-- A module of finite type whose stalk at `x` vanishes carries a neighbourhood of `x` on which
its zero endomorphism is locally surjective. This is the conclusion of Tag 01B8 for the zero
morphism, kept in the section-level form that passes to smaller neighbourhoods. -/
private lemma exists_nbhd_locallySurjOn_zero (K : SheafOfModules.{u} R) [K.IsFiniteType] (x : X)
    (hx : IsZero (TopCat.Presheaf.stalk (C := Ab.{u}) K.val.presheaf x)) :
    ∃ W : Opens X, x ∈ W ∧
      Stacks.SheafOfModules.LocallySurjective.LocallySurjOn (X := auxiliaryRingedSpace X) (0 : K ⟶
        K) W := by
  have hsub := AddCommGrpCat.subsingleton_of_isZero hx
  have hsurj : Stacks.SheafOfModules.LocallySurjective.SurjOnStalk (X := auxiliaryRingedSpace X) (R
    := R) (0 : K ⟶ K) x :=
    fun _ => ⟨0, hsub.elim _ _⟩
  have hK : SheafOfModules.IsFiniteType.{u, u, u} K := inferInstance
  exact Stacks.SheafOfModules.LocallySurjective.exists_nbhd_locallySurjOn (X := auxiliaryRingedSpace
    X) (0 : K ⟶ K) hK x hsurj

/-- The stalk of the kernel of `φ` at `x` vanishes as soon as `φ` is injective on the stalk at
`x`: the inclusion of the kernel is a monomorphism, hence injective on sections and so on
stalks, and a germ of the kernel is carried by it into the kernel of the stalk map of `φ`. -/
private lemma isZero_stalk_kernel_of_stalk_injective {F G : SheafOfModules.{u} R} (φ : G ⟶ F)
    (x : X)
    (hx : Function.Injective
      (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf R.obj).map φ.val)))) :
    IsZero (TopCat.Presheaf.stalk (C := Ab.{u}) (kernel φ).val.presheaf x) := by
  have hmono : Mono ((PresheafOfModules.toPresheaf R.obj).map (kernel.ι φ).val) :=
    Functor.map_mono (PresheafOfModules.toPresheaf R.obj)
      ((SheafOfModules.forget R).map (kernel.ι φ))
  have happ : ∀ U : Opens X, Function.Injective (ConcreteCategory.hom
      (((PresheafOfModules.toPresheaf R.obj).map (kernel.ι φ).val).app (op U))) := fun U =>
    (ConcreteCategory.mono_iff_injective_of_preservesPullback _).1
      ((NatTrans.mono_iff_mono_app _).1 hmono (op U))
  have hinj := TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective happ x
  have hz : ((PresheafOfModules.toPresheaf R.obj).map (kernel.ι φ).val) ≫
      ((PresheafOfModules.toPresheaf R.obj).map φ.val) = 0 := by
    rw [← Functor.map_comp, show (kernel.ι φ).val ≫ φ.val = 0 from
      congrArg (·.val) (kernel.condition φ)]
    exact Functor.map_zero _ _ _
  have hcomp : ∀ (V : Opens X)
      (k : ToType
        (((PresheafOfModules.toPresheaf R.obj).obj (kernel φ).val).obj (op V))),
      (ConcreteCategory.hom
          (((PresheafOfModules.toPresheaf R.obj).map φ.val).app (op V)))
        ((ConcreteCategory.hom
          (((PresheafOfModules.toPresheaf R.obj).map (kernel.ι φ).val).app (op V))) k) = 0 := by
    intro V k
    rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, hz, NatTrans.app_zero]
    rfl
  have hzero : ∀ z : ToType (TopCat.Presheaf.stalk
      ((PresheafOfModules.toPresheaf R.obj).obj (kernel φ).val) x), z = 0 := by
    intro z
    obtain ⟨V, hxV, k, rfl⟩ := TopCat.Presheaf.exists_germ_eq
      ((PresheafOfModules.toPresheaf R.obj).obj (kernel φ).val) z
    refine hinj (Eq.trans ?_ (map_zero _).symm)
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    refine hx (Eq.trans ?_ (map_zero _).symm)
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, hcomp V k]
    exact map_zero _
  exact @AddCommGrpCat.isZero_of_subsingleton _ ⟨fun a b => by rw [hzero a, hzero b]⟩

/-- **Stacks Project, Tag 01Y3.** A morphism from a module of finite type to a coherent module
which is injective on one stalk is a monomorphism after restriction to a neighbourhood of that
point. -/
@[stacks 01C0]
public theorem exists_isMono_over_of_stalk_injective {G F : SheafOfModules.{u} R}
    (φ : G ⟶ F) [G.IsFiniteType] [_root_.SheafOfModules.IsCoherent F] (x : X)
    (hx : Function.Injective
      (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf R.obj).map φ.val)))) :
    ∃ U : Opens X, x ∈ U ∧ Mono (φ.over U) := by
  have _hs : Stacks.SheafOfModules.IsCoherent F :=
    Stacks.AlgebraicGeometry.ProperMapping.stacksIsCoherent
      (inferInstance : _root_.SheafOfModules.IsCoherent F)
  have hK : (kernel φ).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_kernel_of_isCoherent φ
  obtain ⟨W, hxW, hW⟩ :=
    exists_nbhd_locallySurjOn_zero (kernel φ) x (isZero_stalk_kernel_of_stalk_injective φ x hx)
  refine ⟨W, hxW, Preadditive.mono_of_isZero_kernel _ ?_⟩
  exact ((isZero_over_of_locallySurjOn_zero (kernel φ) W hW).of_iso
    (Stacks.SheafOfModules.overKernelIso φ W).symm)

-- Tag 01Y3 part (2) is Tag 01C0, so the two tags name the one statement above and part (2) is
-- registered by name. A `/-- -/` docstring here is a parse error: `add_to_stacks` is a command,
-- not a declaration, so the doc comment has nothing to attach to.
add_to_stacks 01Y3 "part (2)"
  AlgebraicGeometry.exists_isMono_over_of_stalk_injective

end AlgebraicGeometry
