module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import StacksFrontier.Topology.Sheaves.Modules.Colimits

/-!
# The skyscraper sheaf of modules at a point

Let `X` be a topological space, `O` a sheaf of rings on the site of open subsets of `X`, and
`x : X`. Write `i_x : ({x}, O_x) ⟶ (X, O)` for the inclusion of the point, read as a morphism
of ringed spaces. This file constructs the direct image `i_{x,*}` of modules along it, as a
functor from modules over the stalk ring `O_x` to sheaves of `O`-modules, and proves that it is
exact and that taking the stalk at `x` again returns the module one started with.

## The construction

The sections of `i_{x,*} M` over an open `U` are `M` when `x ∈ U` and zero otherwise. Rather
than writing that with a case distinction on `x ∈ U`, the sections are taken to be the
functions `PLift (x ∈ U) → M` from the *proposition* `x ∈ U`, viewed as a type, to `M`. Since
a proposition has at most one proof, that type of functions is `M` when `x ∈ U` and a single
point otherwise, so this is the skyscraper; but it is a type that depends on `U` only through
an honest function type, so:

* the restriction maps are precomposition with the implication `x ∈ V → x ∈ U`, and the two
  presheaf axioms hold by proof irrelevance, with no `eqToHom`;
* the `O(U)`-module structure is `(r • s) h = (germ r) • s h`, which may use the germ map at
  `x` because `h : x ∈ U` is available inside the function body — exactly the point at which
  a case distinction would otherwise be forced;
* the value at an open not containing `x` is a subsingleton, hence a zero module, by
  definitional unfolding rather than by rewriting along a branch of an `if`.

A construction by `if x ∈ U then _ else _` has to carry the equalities `(if .. ) = M` as
`eqToHom`s through every proof, because the decidability instance is the classical one and so
the `if` never reduces.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.skyscraperAb`: the underlying presheaf of abelian groups.
* `AlgebraicGeometry.SheafOfModules.skyscraperModule`: its `O(U)`-module structure.
* `AlgebraicGeometry.SheafOfModules.skyscraperVal`: the underlying presheaf of `O`-modules.
* `AlgebraicGeometry.SheafOfModules.skyscraperObj`: the skyscraper sheaf of `O`-modules.
* `AlgebraicGeometry.SheafOfModules.skyscraperFunctor`: the direct image `i_{x,*}`, as a
  functor from `O_x`-modules to sheaves of `O`-modules.

## Main results

* `AlgebraicGeometry.SheafOfModules.isSheaf_skyscraperAb`: the skyscraper is a sheaf. Proved
  from the unique-gluing form of the sheaf condition: a compatible family has a gluing because
  `x` lies in one member of any cover of an open containing it, and the gluing is unique
  because a section over an open containing `x` is determined by its value at any proof that
  it does.
* `AlgebraicGeometry.SheafOfModules.skyscraperStalkIso`: the stalk at `x` of `i_{x,*} M` is
  `M`, naturally in `M`. Surjectivity of the comparison map is proof irrelevance — a section
  over `U ∋ x` is the constant section at its value — and injectivity is that a germ vanishing
  at `x` vanishes on a neighbourhood.
* `AlgebraicGeometry.SheafOfModules.skyscraperFunctor_preservesFiniteLimits` and
  `AlgebraicGeometry.SheafOfModules.skyscraperFunctor_preservesFiniteColimits`: `i_{x,*}` is
  exact. Both are checked one open set at a time: over an open containing `x` the functor is
  restriction of scalars along the germ map, which is exact, and over any other open it is
  zero. Finite limits and colimits of presheaves of modules are computed open set by open set,
  and the inclusion of sheaves of modules into presheaves of modules is fully faithful, hence
  reflects both.
* `AlgebraicGeometry.SheafOfModules.skyscraperFunctor_additive`: `i_{x,*}` is additive.

## References

* [Stacks Project, Tag 009A](https://stacks.math.columbia.edu/tag/009A)
* [Stacks Project, Tag 06YB](https://stacks.math.columbia.edu/tag/06YB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

noncomputable section

namespace AlgebraicGeometry.SheafOfModules

variable {X : TopCat.{u}}
  (O : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (x : X)

section Construction

variable (M : ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x))

/-- The underlying presheaf of abelian groups of the skyscraper sheaf at `x` with value `M`:
its sections over `U` are the functions from the proposition `x ∈ U` to `M`, which is `M` when
`x ∈ U` and the zero group otherwise, and its restriction maps are precomposition with the
implications between those propositions. -/
def skyscraperAb : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (PLift (x ∈ U.unop) → M)
  map {_ _} i := AddCommGrpCat.ofHom
    { toFun := fun s h => s ⟨leOfHom i.unop h.down⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

/-- A restriction map of `skyscraperAb` evaluates a section at the implied proof of membership. -/
@[simp]
theorem skyscraperAb_map_apply {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (s : PLift (x ∈ U.unop) → M) (h : PLift (x ∈ V.unop)) :
    ((skyscraperAb O x M).map i).hom s h = s ⟨leOfHom i.unop h.down⟩ :=
  rfl

/-- The germ map at `x`, read as a ring homomorphism from `O(U)` to the functions from
`x ∈ U` to the stalk ring: a scalar is sent to the function constant at its germ.

Writing the germ map this way is what lets the module structure below be assembled from the
componentwise one, rather than having its seven axioms checked by hand: the germ at `x` of a
section over `U` needs a proof that `x ∈ U`, and in a function out of `x ∈ U` such a proof is
available. -/
def skyscraperGerm (U : (Opens X)ᵒᵖ) :
    O.obj.obj U →+* (PLift (x ∈ U.unop) →
      TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x) where
  toFun r := fun h =>
    (TopCat.Presheaf.germ (C := RingCat.{u}) (X := X) O.obj U.unop x h.down).hom r
  map_one' := funext fun _ => map_one _
  map_mul' _ _ := funext fun _ => map_mul _ _ _
  map_zero' := funext fun _ => map_zero _
  map_add' _ _ := funext fun _ => map_add _ _ _

/-- The `O(U)`-module structure on the sections of the skyscraper sheaf over `U`: a section
is scaled by scaling its value by the germ at `x` of the scalar. This is the componentwise
module structure of `Pi.module'`, restricted along `skyscraperGerm`.

It is stated at the sections of `skyscraperAb` rather than at the function type they unfold
to, because that is the form in which `PresheafOfModules.ofPresheaf` asks for it and `def`s
are not unfolded by instance search. -/
@[instance_reducible]
def skyscraperModule (U : (Opens X)ᵒᵖ) :
    Module (O.obj.obj U) ((skyscraperAb O x M).obj U) :=
  Module.compHom (PLift (x ∈ U.unop) → M) (skyscraperGerm O x U)

attribute [local instance] skyscraperModule

/-- A scalar `r : O(U)` acts on a section of the skyscraper by its germ at `x` on the value. -/
theorem skyscraperModule_smul_apply (U : (Opens X)ᵒᵖ) (r : O.obj.obj U)
    (s : (skyscraperAb O x M).obj U) (h : PLift (x ∈ U.unop)) :
    (r • s) h =
      (TopCat.Presheaf.germ (C := RingCat.{u}) (X := X) O.obj U.unop x h.down).hom r • s h :=
  rfl

/-- The underlying presheaf of `O`-modules of the skyscraper sheaf at `x` with value `M`.

The restriction maps are semilinear because the germ at `x` of a restricted section is the
germ of the section. -/
def skyscraperVal : PresheafOfModules.{u} O.obj :=
  PresheafOfModules.ofPresheaf (skyscraperAb O x M) (fun {_U _V} i r s => funext fun h =>
    congrArg
      (fun t : TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x =>
        t • s ⟨leOfHom i.unop h.down⟩)
      (TopCat.Presheaf.germ_res_apply O.obj i.unop x h.down r).symm)

/-- The skyscraper presheaf of modules is a sheaf.

A compatible family of sections on a cover of `U` has a gluing: if `x ∈ U` then `x` lies in
some member of the cover, and compatibility says the values there of any two members
containing `x` agree. The gluing is unique because a section over an open containing `x` is
the constant function at its value on any proof of membership. -/
theorem isSheaf_skyscraperAb :
    CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X) (skyscraperAb O x M) := by
  refine (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (skyscraperAb O x M)).mpr ?_
  intro ι U sf hsf
  -- Compatibility, read off at the point: all members of the cover containing `x` carry the
  -- same value there.
  have key : ∀ (i j : ι) (hi : x ∈ U i) (hj : x ∈ U j), sf i ⟨hi⟩ = sf j ⟨hj⟩ :=
    fun i j hi hj => congrFun (hsf i j) ⟨⟨hi, hj⟩⟩
  refine ⟨fun h => sf _
    ⟨(Opens.mem_iSup.mp h.down).choose_spec⟩, fun i => funext fun h => key _ i _ h.down, ?_⟩
  exact fun t ht => funext fun h => congrFun (ht _)
    ⟨(Opens.mem_iSup.mp h.down).choose_spec⟩

/-- **The skyscraper sheaf of modules** `i_{x,*} M` at `x` with value an `O_x`-module `M`: the
sheaf of `O`-modules whose sections over `U` are `M` when `x ∈ U` and zero otherwise, with
`O(U)` acting through its germ at `x`. -/
def skyscraperObj : _root_.SheafOfModules.{u} O where
  val := skyscraperVal O x M
  isSheaf := isSheaf_skyscraperAb O x M

end Construction

section Functor

attribute [local instance] skyscraperModule

variable {M N : ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x)}

/-- The morphism of skyscraper presheaves of abelian groups induced by a linear map of their
values: it applies the map to the value of a section. -/
def skyscraperAbMap (f : M ⟶ N) : skyscraperAb O x M ⟶ skyscraperAb O x N where
  app _ := AddCommGrpCat.ofHom
    { toFun := fun s h => f.hom (s h)
      map_zero' := funext fun _ => map_zero f.hom
      map_add' := fun _ _ => funext fun _ => map_add f.hom _ _ }
  naturality := by
    intros
    rfl

/-- The morphism of skyscraper sheaves of modules induced by a linear map of their values. It
is linear because the scalar action on either side is through the same germ map. -/
def skyscraperMap (f : M ⟶ N) : skyscraperObj O x M ⟶ skyscraperObj O x N where
  val := PresheafOfModules.homMk (skyscraperAbMap O x f)
    (fun _ _ _ => funext fun _ => map_smul f.hom _ _)

/-- **The direct image of modules along the inclusion of a point.** Pushing an `O_x`-module
forward along `i_x : ({x}, O_x) ⟶ (X, O)` is the skyscraper sheaf at `x` with that value, and
the assignment is functorial. -/
def skyscraperFunctor :
    ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x) ⥤
      _root_.SheafOfModules.{u} O where
  obj M := skyscraperObj O x M
  map f := skyscraperMap O x f
  map_id _ := by
    ext
    rfl
  map_comp _ _ := by
    ext
    rfl

end Functor

section Stalk

attribute [local instance] skyscraperModule

variable (M : ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x))

/-- A constant section of the skyscraper over an open containing `x` has the same germ at `x`
whichever open it is taken over: restricting a constant section is again the constant
section. -/
theorem germ_skyscraper_const (U : Opens X) (hxU : x ∈ U) (m : M) :
    (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X)
        (skyscraperVal O x M).presheaf U x hxU).hom (fun _ => m) =
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X)
        (skyscraperVal O x M).presheaf ⊤ x trivial).hom (fun _ => m) :=
  TopCat.Presheaf.germ_res_apply (skyscraperVal O x M).presheaf (homOfLE le_top) x hxU
    (fun _ => m)

/-- The comparison map from an `O_x`-module to the stalk at `x` of its skyscraper sheaf: a
module element goes to the germ of the constant section it determines.

It is linear because a scalar on the stalk is the germ of a scalar `r'` on some neighbourhood
`U` of `x`, and over `U` the constant section at `r • m` *is* `r'` times the constant section
at `m`, by the very definition of the module structure on the skyscraper. -/
def toSkyscraperStalk : M ⟶ stalkObj O x (skyscraperObj O x M) :=
  ModuleCat.ofHom
    { toFun := fun m => (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X)
        (skyscraperVal O x M).presheaf ⊤ x trivial).hom (fun _ => m)
      map_add' := fun _ _ => map_add _ _ _
      map_smul' := fun r m => by
        obtain ⟨U, hxU, r', hr'⟩ := TopCat.Presheaf.exists_germ_eq O.obj r
        have hconst : (r' • (show (skyscraperVal O x M).obj (op U) from fun _ => m)) =
            (fun _ => r • m) :=
          funext fun _ => congrArg (fun t => t • m) hr'
        calc (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X)
                (skyscraperVal O x M).presheaf ⊤ x trivial).hom (fun _ => r • m)
            = (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X)
                (skyscraperVal O x M).presheaf U x hxU).hom (fun _ => r • m) :=
              (germ_skyscraper_const O x M U hxU (r • m)).symm
          _ = (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X)
                (skyscraperVal O x M).presheaf U x hxU).hom
              (r' • (show (skyscraperVal O x M).obj (op U) from fun _ => m)) :=
              congrArg _ hconst.symm
          _ = (TopCat.Presheaf.germ (C := RingCat.{u}) (X := X) O.obj U x hxU).hom r' •
              (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X)
                (skyscraperVal O x M).presheaf U x hxU).hom (fun _ => m) :=
              germ_hom_smul O x (skyscraperVal O x M) U hxU r' _
          _ = r • (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X)
                (skyscraperVal O x M).presheaf U x hxU).hom (fun _ => m) :=
              congrArg (fun t => t • _) hr'
          _ = r • (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X)
                (skyscraperVal O x M).presheaf ⊤ x trivial).hom (fun _ => m) :=
              congrArg (fun t => r • t) (germ_skyscraper_const O x M U hxU m) }

/-- The comparison map `toSkyscraperStalk` is injective. -/
theorem toSkyscraperStalk_injective : Function.Injective (toSkyscraperStalk O x M).hom := by
  intro m₁ m₂ hm
  obtain ⟨W, hxW, iU, iV, e⟩ :=
    TopCat.Presheaf.germ_eq (U := ⊤) (V := ⊤) (skyscraperVal O x M).presheaf x trivial trivial
      (fun _ => m₁) (fun _ => m₂) hm
  exact congrFun e ⟨hxW⟩

/-- The comparison map `toSkyscraperStalk` is surjective. -/
theorem toSkyscraperStalk_surjective : Function.Surjective (toSkyscraperStalk O x M).hom := by
  intro t
  obtain ⟨U, hxU, s, rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq (skyscraperVal O x M).presheaf t
  exact ⟨s ⟨hxU⟩, (germ_skyscraper_const O x M U hxU (s ⟨hxU⟩)).symm⟩

/-- The stalk at `x` of the skyscraper sheaf at `x` with value `M` is `M`.

The comparison map `toSkyscraperStalk` is onto because every element of the stalk is the germ
of a section over some neighbourhood of `x`, and a section of the skyscraper over a
neighbourhood of `x` is the constant section at its value; it is injective because two germs
at `x` that agree come from sections that agree on a neighbourhood of `x`, and for constant
sections that forces the values to agree. -/
def skyscraperStalkEquiv : M ≃ₗ[TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x]
    stalkObj O x (skyscraperObj O x M) :=
  LinearEquiv.ofBijective (toSkyscraperStalk O x M).hom
    ⟨toSkyscraperStalk_injective O x M, toSkyscraperStalk_surjective O x M⟩

/-- The stalk at `x` of the skyscraper sheaf at `x` with value `M`, as an isomorphism of
`O_x`-modules onto `M`. -/
def skyscraperStalkIsoObj : stalkObj O x (skyscraperObj O x M) ≅ M where
  hom := ModuleCat.ofHom (skyscraperStalkEquiv O x M).symm.toLinearMap
  inv := toSkyscraperStalk O x M
  hom_inv_id := ModuleCat.hom_ext (LinearMap.ext fun t =>
    (skyscraperStalkEquiv O x M).apply_symm_apply t)
  inv_hom_id := ModuleCat.hom_ext (LinearMap.ext fun m =>
    (skyscraperStalkEquiv O x M).symm_apply_apply m)

/-- **Taking the stalk at `x` of the skyscraper at `x` returns the module one started with**,
naturally in the module. This is the unit of the point inclusion being an isomorphism:
`i_x^{-1} i_{x,*} ≅ 𝟭`. -/
def skyscraperStalkIso : skyscraperFunctor O x ⋙ stalkFunctor O x ≅ 𝟭 _ :=
  (NatIso.ofComponents (fun M => (skyscraperStalkIsoObj O x M).symm) (fun {M N} f => by
    ext m
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply (C := AddCommGrpCat.{u}) ⊤ x trivial
      ((PresheafOfModules.toPresheaf O.obj).map (skyscraperMap O x f).val) (fun _ => m)).symm)).symm

end Stalk

section Exactness

attribute [local instance] skyscraperModule

/-- The sections of the skyscraper over a fixed open set, as a functor of the module: the
composite of the skyscraper functor with evaluation at that open set. -/
def skyscraperEval (U : (Opens X)ᵒᵖ) :
    ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x) ⥤
      ModuleCat.{u} (O.obj.obj U) :=
  skyscraperFunctor O x ⋙ _root_.SheafOfModules.forget O ⋙
    PresheafOfModules.evaluation O.obj U

/-- Over an open set containing `x`, the sections of the skyscraper are the module itself,
with `O(U)` acting through its germ at `x`: evaluation of the skyscraper there is restriction
of scalars along the germ map. -/
def skyscraperEvalIso (U : (Opens X)ᵒᵖ) (hxU : x ∈ U.unop) :
    skyscraperEval O x U ≅ ModuleCat.restrictScalars
      (TopCat.Presheaf.germ (C := RingCat.{u}) (X := X) O.obj U.unop x hxU).hom :=
  NatIso.ofComponents
    (fun M => LinearEquiv.toModuleIso
      (X₁ := (skyscraperEval O x U).obj M)
      (X₂ := (ModuleCat.restrictScalars
        (TopCat.Presheaf.germ (C := RingCat.{u}) (X := X) O.obj U.unop x hxU).hom).obj M)
      (g₁ := ModuleCat.isAddCommGroup _) (m₁ := ModuleCat.isModule _)
      (g₂ := ModuleCat.isAddCommGroup _) (m₂ := ModuleCat.isModule _)
      { toFun := fun s => s ⟨hxU⟩
        invFun := fun m _ => m
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl })
    (fun _ => rfl)

/-- Over an open set not containing `x`, the skyscraper has no sections beyond zero. -/
theorem isZero_skyscraperEval (U : (Opens X)ᵒᵖ) (hxU : x ∉ U.unop) :
    IsZero (skyscraperEval O x U) := by
  rw [IsZero.iff_id_eq_zero]
  ext M s
  exact funext fun h => absurd h.down hxU

/-- The sections of the skyscraper over a fixed open set preserve finite limits. -/
instance skyscraperEval_preservesFiniteLimits (U : (Opens X)ᵒᵖ) :
    PreservesFiniteLimits (skyscraperEval O x U) := by
  by_cases hxU : x ∈ U.unop
  · have : PreservesFiniteLimits (ModuleCat.restrictScalars.{u}
        (TopCat.Presheaf.germ (C := RingCat.{u}) (X := X) O.obj U.unop x hxU).hom) :=
      ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
    exact preservesFiniteLimits_of_natIso (skyscraperEvalIso O x U hxU).symm
  · have : PreservesLimitsOfSize.{0, 0} (skyscraperEval O x U) :=
      Functor.preservesLimitsOfSize_of_isZero _ (isZero_skyscraperEval O x U hxU)
    exact ⟨fun _ _ _ => inferInstance⟩

/-- The sections of the skyscraper over a fixed open set preserve finite colimits. -/
instance skyscraperEval_preservesFiniteColimits (U : (Opens X)ᵒᵖ) :
    PreservesFiniteColimits (skyscraperEval O x U) := by
  by_cases hxU : x ∈ U.unop
  · have : PreservesFiniteColimits (ModuleCat.restrictScalars.{u}
        (TopCat.Presheaf.germ (C := RingCat.{u}) (X := X) O.obj U.unop x hxU).hom) :=
      ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
    exact preservesFiniteColimits_of_natIso (skyscraperEvalIso O x U hxU).symm
  · have : PreservesColimitsOfSize.{0, 0} (skyscraperEval O x U) :=
      Functor.preservesColimitsOfSize_of_isZero _ (isZero_skyscraperEval O x U hxU)
    exact ⟨fun _ _ _ => inferInstance⟩

/-- The skyscraper functor followed by the inclusion of sheaves of modules into presheaves of
modules preserves finite limits: finite limits of presheaves of modules are detected open set
by open set, and over each open set the skyscraper is either restriction of scalars along a
germ map or zero. -/
instance skyscraperForget_preservesFiniteLimits :
    PreservesFiniteLimits (skyscraperFunctor O x ⋙ _root_.SheafOfModules.forget O) :=
  ⟨fun _ _ _ => ⟨fun {_} => ⟨fun {_c} hc =>
    ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _
      (fun U => isLimitOfPreserves (skyscraperEval O x U) hc)⟩⟩⟩⟩

/-- The skyscraper functor followed by the inclusion of sheaves of modules into presheaves of
modules preserves finite colimits. This is not obtained from exactness of sheafification: the
colimit of a diagram of skyscrapers computed open set by open set is again a skyscraper, hence
already a sheaf, which is what lets the sheaf-level colimit be read off the presheaf-level one
below. -/
instance skyscraperForget_preservesFiniteColimits :
    PreservesFiniteColimits (skyscraperFunctor O x ⋙ _root_.SheafOfModules.forget O) :=
  ⟨fun _ _ _ => ⟨fun {_} => ⟨fun {_c} hc =>
    ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _
      (fun U => isColimitOfPreserves (skyscraperEval O x U) hc)⟩⟩⟩⟩

/-- **The skyscraper functor is left exact.** It is a limit of its values on open sets, each of
which is restriction of scalars along a germ map or zero, and the inclusion of sheaves of
modules into presheaves of modules is fully faithful, hence reflects limits. -/
instance skyscraperFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (skyscraperFunctor O x) :=
  preservesFiniteLimits_of_reflects_of_preserves (skyscraperFunctor O x)
    (_root_.SheafOfModules.forget O)

/-- **The skyscraper functor is right exact.** -/
instance skyscraperFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (skyscraperFunctor O x) :=
  preservesFiniteColimits_of_reflects_of_preserves (skyscraperFunctor O x)
    (_root_.SheafOfModules.forget O)

/-- The skyscraper functor is additive: a sum of linear maps acts on a section by acting on
its value. -/
instance skyscraperFunctor_additive : (skyscraperFunctor O x).Additive where
  map_add := by
    intros
    ext
    rfl

end Exactness

end AlgebraicGeometry.SheafOfModules

end

end
