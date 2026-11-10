module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.Localization
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteFiniteTypeBridge

/-!
# The restriction of a sheaf of ideals of finite type is of finite type

Let `(𝒞, 𝒪)` be a ringed site, `ℐ ⊂ 𝒪` a sheaf of ideals and `U` an object of `𝒞`. The
restriction `ℐ|_U = AlgebraicGeometry.RingedSite.overIdeal ℐ U` to the slice site `𝒞/U` has as
sections over `W` the sections of `ℐ` over `W.left`. This file shows that `ℐ|_U` is of finite
type when `ℐ` is, in both the sectionwise and Mathlib's categorical sense.

## Main results

* `AlgebraicGeometry.RingedSite.generates_overIdeal`: a finite family of sections of `ℐ` over `V`
  generating `ℐ` restricts, along any `W.left ⟶ V` with `W` an object of `𝒞/U`, to a family
  generating `ℐ|_U` over `W`.
* `AlgebraicGeometry.RingedSite.presheaf_isFiniteType_overIdeal`: the sectionwise statement.
* `AlgebraicGeometry.RingedSite.isFiniteType_overIdeal`: the statement at Mathlib's
  `SheafOfModules.IsFiniteType`, as an instance.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u v w

namespace AlgebraicGeometry.RingedSite

section Sectionwise

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  (I : SheafOfModules.Submodule (SheafOfModules.unit R)) (U : C)

/-- **Generators of `ℐ` over `V` restrict to generators of `ℐ|_U`** over every object `W` of the
slice site `𝒞/U` together with an arrow `W.left ⟶ V` of `𝒞`. A section of `ℐ|_U` over `T ⟶ W` is
a section of `ℐ` over `T.left`, which is locally a combination of the generators along a covering
sieve of `T.left`; that sieve read on `𝒞/U` is covering for the slice topology. -/
theorem generates_overIdeal {V : C} {n : ℕ} (s : Fin n → I.toSheafOfModules.val.obj (op V))
    (hs : PresheafOfModules.Generates J I.toSheafOfModules.val s) (W : Over U)
    (φ : W.left ⟶ V) :
    PresheafOfModules.Generates (J.over U) (overIdeal I U).toSheafOfModules.val
      (fun i => (I.toSheafOfModules.val.map φ.op (s i) :
        I.toSheafOfModules.val.obj (op W.left))) := by
  intro T f x
  obtain ⟨S, hS, hgen⟩ := hs T.left (f.left ≫ φ) x
  refine ⟨(Sieve.overEquiv T).symm S, J.overEquiv_symm_mem_over T S hS, fun Z g hg => ?_⟩
  obtain ⟨a, ha⟩ := hgen Z.left g.left hg
  refine ⟨a, ?_⟩
  have hc (i : Fin n) :
      I.toSheafOfModules.val.restrictₛₗ (g.left ≫ f.left).op
          (I.toSheafOfModules.val.map φ.op (s i)) =
        I.toSheafOfModules.val.restrictₛₗ (g.left ≫ f.left ≫ φ).op (s i) := by
    change I.toSheafOfModules.val.map (g.left ≫ f.left).op
        (I.toSheafOfModules.val.map φ.op (s i)) =
      I.toSheafOfModules.val.map (g.left ≫ f.left ≫ φ).op (s i)
    rw [← PresheafOfModules.map_comp_apply]
    exact I.toSheafOfModules.val.congr_map_apply
      (by rw [← op_comp, Category.assoc]) (s i)
  change (∑ i, a i • I.toSheafOfModules.val.restrictₛₗ (g.left ≫ f.left).op
      (I.toSheafOfModules.val.map φ.op (s i))) =
    I.toSheafOfModules.val.restrictₛₗ g.left.op x
  simpa only [hc] using ha

/-- **`ℐ|_U` is of finite type, sectionwise, when `ℐ` is.** The covering family is indexed by
the triples `(i, W, W.left ⟶ V_i)` for `{V_i}` a covering family of `𝒞` carrying generators of
`ℐ`; it covers `𝒞/U` because a sieve on `T` is covering for the slice topology exactly when its
image on `T.left` is covering, and the image of this one contains the sieve of `T.left` generated
by the `V_i`. -/
theorem presheaf_isFiniteType_overIdeal
    (hI : PresheafOfModules.IsFiniteType J I.toSheafOfModules.val) :
    PresheafOfModules.IsFiniteType (J.over U) (overIdeal I U).toSheafOfModules.val := by
  obtain ⟨κ, V, hV, hgen⟩ := hI.exists_generators
  choose n s hs using hgen
  refine ⟨⟨Σ i : κ, Σ W : Over U, W.left ⟶ V i, fun p => p.2.1, ?_,
    fun p => ⟨n p.1, _, generates_overIdeal I U (s p.1) (hs p.1) p.2.1 p.2.2⟩⟩⟩
  intro T
  rw [GrothendieckTopology.mem_over_iff]
  refine J.superset_covering ?_ (hV T.left)
  rintro Z g ⟨i, ⟨h⟩⟩
  rw [Sieve.overEquiv_iff]
  exact ⟨⟨i, Over.mk (g ≫ T.hom), h⟩, ⟨𝟙 _⟩⟩

end Sectionwise

variable (X : RingedSite.{u, u, u})
  (I : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) (U : X.C)

/-- **The restriction of a sheaf of ideals of finite type to a slice site is of finite type**, at
Mathlib's categorical finite-type condition. -/
instance isFiniteType_overIdeal [I.toSheafOfModules.IsFiniteType] :
    (overIdeal I U).toSheafOfModules.IsFiniteType :=
  SheafOfModules.isFiniteType_of_presheaf_isFiniteType _
    (presheaf_isFiniteType_overIdeal I U
      (Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteType I.toSheafOfModules
        inferInstance))

/-- `isFiniteType_overIdeal` with the structure sheaf of the slice spelled as that of the ringed
site `X.over U`, which is the spelling a statement about the ringed site `X.over U` asks for and
which instance search does not identify with the restriction of the structure sheaf of `X`. -/
instance isFiniteType_overIdeal_over [I.toSheafOfModules.IsFiniteType] :
    (SheafOfModules.Submodule.toSheafOfModules
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O))
      (M := SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)))
      (overIdeal I U)).IsFiniteType :=
  isFiniteType_overIdeal X I U

end AlgebraicGeometry.RingedSite

end
