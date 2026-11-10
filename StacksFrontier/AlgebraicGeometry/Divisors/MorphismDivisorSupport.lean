module

public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismDivisorPower
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Sections
public import StacksFrontier.AlgebraicGeometry.SectionProduct.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree

/-!
# Where a morphism of invertible modules is an isomorphism, its divisor is absent

A morphism `σ : L ⟶ L'` of `𝒪_X`-modules is the same thing as a global section of
`SheafHom(L, L')`, and a section of the internal hom over an open `W` is a morphism on the
slice site over `W`, so it has a component over every smaller open.  For the section attached
to `σ` that component is `σ` itself.  This file reads the nonvanishing locus of that section
off those components: if the germ of the section lies in `𝔪_x · SheafHom(L, L')_x`, then `σ`
carries the whole stalk `L_x` into `𝔪_x · L'_x`, which is impossible when the stalk map of `σ`
at `x` is surjective and `L'` is invertible.

Transported across the comparison `L' ⊗ L^∨ ≅ SheafHom(L, L')`, this says that the global
section of `L' ⊗ L^∨` attached to `σ` does not vanish where `σ` is a stalkwise isomorphism; so
the zero scheme `AlgebraicGeometry.morphismZeroScheme` of `σ` is supported where `σ` is not.

## Main results

* `AlgebraicGeometry.notMem_maximalSmul_germ_internalHomSection`: the section of the internal
  hom attached to `σ` does not vanish at a point where the stalk map of `σ` is surjective.
* `AlgebraicGeometry.mem_nonvanishingLocus_homTensorDualSection_of_surjective_stalk`: the same
  for the section of `L' ⊗ L^∨`.
* `AlgebraicGeometry.supportSet_morphismZeroScheme_subset_of_surjective_stalk_off`: the zero
  scheme of `σ` is supported inside any set outside which the stalk maps of `σ` are surjective.
* `AlgebraicGeometry.exists_pow_tensorIso_of_surjective_stalk_off` and
  `AlgebraicGeometry.exists_pow_tensorIso_detMap_of_surjective_stalk_off`: a nonzero morphism of
  invertible modules which is a stalkwise epimorphism away from an integral effective Cartier
  divisor `D` exhibits the target as the twist of the source by `D ^ k`.
* `AlgebraicGeometry.mem_ideal_morphismZeroScheme`: the ideal of the divisor of `σ` on an affine
  open contains the value at `σ v` of every linear functional on the sections of `L'`.

## Implementation notes

`AlgebraicGeometry.sheafHomSectionApp` is the component of a section of the internal hom at a
smaller open.  Its compatibility with restriction, with addition and with the identification of
the global sections with the morphisms all hold by `rfl`; only compatibility with the scalar
action needs a lemma, `Stacks.SheafOfModules.internalHom_smul_app_apply`.

The passage from the germ to the components is an induction over `𝔪_x · ⊤` with
`Submodule.smul_induction_on`, in the shape
`Stacks.NonvanishingTrivialize.notMem_maximalSmul_germ_basis` uses: the predicate asks for
*some* representative of the germ whose components all land in `𝔪_x · L'_x`, which is what
makes it closed under addition — two representatives are restricted to the intersection of
their domains.

The last section goes the other way round and needs no germ at all: a linear functional on the
sections of `L'` over `U` composed with evaluation at a fixed section of `L` is a linear
functional on the sections of the internal hom, hence, across the comparison with the twist, one
of the generators of the defining ideal of the zero scheme over `U`. Only this inclusion of the
ideal is proved — it is the one that bounds the multiplicity of the divisor from above, which is
what [Stacks, Tag 0B3T] needs; the reverse inclusion would require a trivialization of the
internal hom and is not proved here.

No Nakayama lemma is needed at the end.  `Stacks.SectionProduct.exists_notMem_maximalSmul` says
the stalk of an invertible module is not exhausted by `𝔪_x · L'_x`, and a surjective stalk map
whose image lies in that submodule would exhaust it.

## References

* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
* [Stacks Project, Tag 0882](https://stacks.math.columbia.edu/tag/0882)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

open Stacks.SheafOfModules Stacks.Algebraization

variable {X : Scheme.{u}} (L L' : X.Modules)

/-! ### Components of a section of the internal hom -/

/-- The internal hom `SheafHom(L, L')` of two `𝒪_X`-modules. -/
abbrev sheafHomModule : X.Modules := (sheafHomFunctor X L).obj L'

/-- **The component of a section of `SheafHom(L, L')` at a smaller open.** A section over `W` is
a morphism on the slice site over `W`, and this is its value at `W' ≤ W`. -/
def sheafHomSectionApp {W W' : X.Opens} (hW : W' ≤ W) (a : Γ(sheafHomModule L L', W))
    (v : Γ(L, W')) : Γ(L', W') :=
  (a.app (op (Over.mk (homOfLE hW)))).hom v

variable {L L'}

/-- The component at `W''` of the restriction to `W'` of a section over `W` is its component at
`W''`. -/
@[simp] theorem sheafHomSectionApp_res {W W' W'' : X.Opens} (hW : W' ≤ W) (hW' : W'' ≤ W')
    (a : Γ(sheafHomModule L L', W)) (v : Γ(L, W'')) :
    sheafHomSectionApp L L' hW' (((sheafHomModule L L').presheaf.map (homOfLE hW).op).hom a) v =
      sheafHomSectionApp L L' (hW'.trans hW) a v := rfl

/-- Taking the component of a section of `SheafHom(L, L')` at a smaller open is additive. -/
theorem sheafHomSectionApp_add {W W' : X.Opens} (hW : W' ≤ W) (a b : Γ(sheafHomModule L L', W))
    (v : Γ(L, W')) :
    sheafHomSectionApp L L' hW (a + b) v =
      sheafHomSectionApp L L' hW a v + sheafHomSectionApp L L' hW b v := rfl

/-- The component of `r • a` at `W' ≤ W` is the restriction of `r` to `W'` times the component of
`a`. -/
theorem sheafHomSectionApp_smul {W W' : X.Opens} (hW : W' ≤ W) (r : Γ(X, W))
    (a : Γ(sheafHomModule L L', W)) (v : Γ(L, W')) :
    sheafHomSectionApp L L' hW (r • a) v =
      (X.presheaf.map (homOfLE hW).op).hom r • sheafHomSectionApp L L' hW a v :=
  Stacks.SheafOfModules.internalHom_smul_app_apply X.presheaf L.val L'.val W r a
    (op (Over.mk (homOfLE hW))) v

/-- **The global section of `SheafHom(L, L')` attached to a morphism has `σ` for its
components.** -/
theorem sheafHomSectionApp_internalHomSectionsTop (σ : L ⟶ L') {W : X.Opens} (hW : W ≤ ⊤)
    (v : Γ(L, W)) :
    sheafHomSectionApp L L' hW (internalHomSectionsTopMapAddEquiv L L' σ) v = σ.app W v := rfl

/-! ### The germ of a section of the internal hom -/

/-- `TopCat.Presheaf.germ_res_apply` for a module on a scheme, at the spelling of the germ that
`Stacks.ModuleStalk` uses. -/
private theorem germ_res_hom (M : X.Modules) {W W' : X.Opens} (h : W' ≤ W) (x : X) (hx : x ∈ W')
    (t : Γ(M, W)) :
    (M.presheaf.germ W' x hx).hom ((M.presheaf.map (homOfLE h).op).hom t) =
      (M.presheaf.germ W x (h hx)).hom t :=
  TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE h) x hx t

/-- `TopCat.Presheaf.germ_res_apply` for the structure sheaf, at the same spelling. -/
private theorem germ_res_hom_ring {W W' : X.Opens} (h : W' ≤ W) (x : X) (hx : x ∈ W')
    (t : Γ(X, W)) :
    (X.presheaf.germ W' x hx).hom ((X.presheaf.map (homOfLE h).op).hom t) =
      (X.presheaf.germ W x (h hx)).hom t :=
  TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE h) x hx t

variable (L L')

/-- A germ of `SheafHom(L, L')` at `x` is represented by a section all of whose components send
sections of `L` to sections of `L'` with germ in `𝔪_x · L'_x`.  This is the predicate behind
the induction over `𝔪_x · SheafHom(L, L')_x`. -/
private def EvalGermMem (x : X)
    (m : TopCat.Presheaf.stalk (C := Ab.{u}) (sheafHomModule L L').presheaf x) : Prop :=
  ∃ (W : X.Opens) (hxW : x ∈ W) (a : Γ(sheafHomModule L L', W)),
    ((sheafHomModule L L').presheaf.germ W x hxW).hom a = m ∧
      ∀ (W' : X.Opens) (hW' : W' ≤ W) (hxW' : x ∈ W') (v : Γ(L, W')),
        (L'.presheaf.germ W' x hxW').hom (sheafHomSectionApp L L' hW' a v) ∈
          Stacks.ModuleStalk.maximalSmul L' x

variable {L L'}

/-- Two representatives are restricted to the intersection of their domains and added. -/
private theorem evalGermMem_add {x : X}
    {m m' : TopCat.Presheaf.stalk (C := Ab.{u}) (sheafHomModule L L').presheaf x}
    (hm : EvalGermMem L L' x m) (hm' : EvalGermMem L L' x m') :
    EvalGermMem L L' x (m + m') := by
  obtain ⟨W, hxW, a, ha, hA⟩ := hm
  obtain ⟨V, hxV, b, hb, hB⟩ := hm'
  have hxU : x ∈ W ⊓ V := ⟨hxW, hxV⟩
  refine ⟨W ⊓ V, hxU,
    ((sheafHomModule L L').presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op).hom a +
      ((sheafHomModule L L').presheaf.map (homOfLE (inf_le_right : W ⊓ V ≤ V)).op).hom b, ?_, ?_⟩
  · rw [map_add, germ_res_hom, germ_res_hom, ha, hb]
  · intro W' hW' hxW' v
    rw [sheafHomSectionApp_add, sheafHomSectionApp_res, sheafHomSectionApp_res, map_add]
    exact add_mem (hA W' _ hxW' v) (hB W' _ hxW' v)

/-- A multiple of an arbitrary germ by an element of the maximal ideal has the property: the
components of the scaled section are the scaled components. -/
private theorem evalGermMem_smul {x : X} {r : X.presheaf.stalk x}
    (hr : r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (m : TopCat.Presheaf.stalk (C := Ab.{u}) (sheafHomModule L L').presheaf x) :
    EvalGermMem L L' x (r • m) := by
  obtain ⟨W, hxW, a, ha⟩ :=
    TopCat.Presheaf.exists_germ_eq (sheafHomModule L L').presheaf m
  obtain ⟨V, hxV, ρ, hρ⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf r
  have hxU : x ∈ W ⊓ V := ⟨hxW, hxV⟩
  set ρ' : Γ(X, W ⊓ V) :=
    (X.presheaf.map (homOfLE (inf_le_right : W ⊓ V ≤ V)).op).hom ρ with hρ'
  set a' : Γ(sheafHomModule L L', W ⊓ V) :=
    ((sheafHomModule L L').presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op).hom a with ha'
  have hρx : (X.presheaf.germ (W ⊓ V) x hxU).hom ρ' = r := by
    rw [hρ', germ_res_hom_ring, hρ]
  have hax : ((sheafHomModule L L').presheaf.germ (W ⊓ V) x hxU).hom a' = m := by
    rw [ha', germ_res_hom, ha]
  refine ⟨W ⊓ V, hxU, ρ' • a', ?_, ?_⟩
  · rw [Stacks.ModuleStalk.germ_smul, hρx, hax]
  · intro W' hW' hxW' v
    rw [sheafHomSectionApp_smul, Stacks.ModuleStalk.germ_smul, germ_res_hom_ring, hρx]
    exact Stacks.ModuleStalk.smul_mem_maximalSmul_of_mem_maximalIdeal hr _

/-- Every germ in `𝔪_x · SheafHom(L, L')_x` has a representative all of whose components land
in `𝔪_x · L'_x`. -/
private theorem evalGermMem_of_mem_maximalSmul {x : X}
    {m : TopCat.Presheaf.stalk (C := Ab.{u}) (sheafHomModule L L').presheaf x}
    (hm : m ∈ Stacks.ModuleStalk.maximalSmul (sheafHomModule L L') x) :
    EvalGermMem L L' x m :=
  Submodule.smul_induction_on hm (fun _ hr m _ => evalGermMem_smul hr m)
    fun _ _ h h' => evalGermMem_add h h'

/-- **If the section of the internal hom attached to `σ` vanishes at `x`, then `σ` carries the
stalk `L_x` into `𝔪_x · L'_x`.** -/
theorem mapFun_mem_maximalSmul_of_germ_mem (σ : L ⟶ L') (x : X)
    (hx : ((sheafHomModule L L').presheaf.Γgerm x).hom
        (internalHomSectionsTopMapAddEquiv L L' σ) ∈
      Stacks.ModuleStalk.maximalSmul (sheafHomModule L L') x)
    (m : TopCat.Presheaf.stalk (C := Ab.{u}) L.presheaf x) :
    Stacks.ModuleStalk.mapFun σ x m ∈ Stacks.ModuleStalk.maximalSmul L' x := by
  obtain ⟨W, hxW, a, ha, hA⟩ := evalGermMem_of_mem_maximalSmul hx
  obtain ⟨W₁, hxW₁, i₁, i₂, heq⟩ :=
    TopCat.Presheaf.germ_eq (sheafHomModule L L').presheaf x hxW (by trivial) a
      (internalHomSectionsTopMapAddEquiv L L' σ) ha
  obtain ⟨W₂, hxW₂, v, hv⟩ := TopCat.Presheaf.exists_germ_eq L.presheaf m
  have hxI : x ∈ W₁ ⊓ W₂ := ⟨hxW₁, hxW₂⟩
  set v' : Γ(L, W₁ ⊓ W₂) :=
    (L.presheaf.map (homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)).op).hom v with hv'
  have hvx : (L.presheaf.germ (W₁ ⊓ W₂) x hxI).hom v' = m := by
    rw [hv', germ_res_hom, hv]
  have hle : W₁ ⊓ W₂ ≤ W₁ := inf_le_left
  have heq' : (sheafHomModule L L').presheaf.map (homOfLE i₁.le).op a =
      (sheafHomModule L L').presheaf.map (homOfLE (le_top : W₁ ≤ ⊤)).op
        (internalHomSectionsTopMapAddEquiv L L' σ) := heq
  have key : sheafHomSectionApp L L' (hle.trans i₁.le) a v' = σ.app (W₁ ⊓ W₂) v' :=
    congrArg (fun z => sheafHomSectionApp L L' hle z v') heq'
  have := hA (W₁ ⊓ W₂) (hle.trans i₁.le) hxI v'
  rw [key] at this
  rwa [← hvx, Stacks.ModuleStalk.mapFun_germ]

/-- **The section of `SheafHom(L, L')` attached to `σ` does not vanish where the stalk map of
`σ` is surjective**, for `L'` invertible: otherwise the whole stalk `L'_x` would lie in
`𝔪_x · L'_x`. -/
theorem notMem_maximalSmul_germ_internalHomSection (σ : L ⟶ L') (x : X)
    [Stacks.Ample.IsInvertibleModule X L']
    (hσ : Function.Surjective (Stacks.ModuleStalk.mapFun σ x)) :
    ((sheafHomModule L L').presheaf.Γgerm x).hom
        (internalHomSectionsTopMapAddEquiv L L' σ) ∉
      Stacks.ModuleStalk.maximalSmul (sheafHomModule L L') x := by
  intro hmem
  obtain ⟨w, hw⟩ := Stacks.SectionProduct.exists_notMem_maximalSmul L' x
  obtain ⟨m, rfl⟩ := hσ w
  exact hw (mapFun_mem_maximalSmul_of_germ_mem σ x hmem m)

/-! ### The support of the divisor of a morphism -/

section Support

variable (L L') [IsIntegral X]
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L']

omit [IsIntegral X] [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L'] in
/-- **The comparison `L' ⊗ L^∨ ≅ SheafHom(L, L')` carries the global section attached to `σ` to
the section of the internal hom attached to `σ`.** -/
theorem tensorDualIsoSheafHom_homTensorDualSectionEquiv
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (σ : L ⟶ L') :
    (Scheme.tensorDualIsoSheafHom L L').hom.app ⊤ (Scheme.homTensorDualSectionEquiv L L' σ) =
      internalHomSectionsTopMapAddEquiv L L' σ :=
  (Stacks.SheafOfModules.valAddEquivOfIso (Scheme.tensorDualIsoSheafHom L L')
    (op (⊤ : X.Opens))).apply_symm_apply _

omit [IsIntegral X] [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L'] in
/-- **The section of `L' ⊗ L^∨` attached to `σ` does not vanish where the stalk map of `σ` is
surjective.** -/
theorem mem_nonvanishingLocus_homTensorDualSection_of_surjective_stalk
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [Stacks.Ample.IsInvertibleModule X L'] (σ : L ⟶ L') (x : X)
    (hσ : Function.Surjective (Stacks.ModuleStalk.mapFun σ x)) :
    x ∈ Stacks.Ample.nonvanishingLocus (Scheme.tensorDualTwist L L')
      (Scheme.homTensorDualSectionEquiv L L' σ) := by
  rw [← Stacks.Ample.nonvanishingLocus_congr (Scheme.tensorDualIsoSheafHom L L')
    (Scheme.homTensorDualSectionEquiv L L' σ),
    tensorDualIsoSheafHom_homTensorDualSectionEquiv L L' σ]
  exact notMem_maximalSmul_germ_internalHomSection σ x hσ

/-- **The divisor of a nonzero morphism of invertible modules on an integral scheme is supported
where the morphism fails to be a stalkwise epimorphism.** -/
theorem supportSet_morphismZeroScheme_subset_of_surjective_stalk_off {σ : L ⟶ L'} (hσ : σ ≠ 0)
    (Z : Set X) (hoff : ∀ x : X, x ∉ Z → Function.Surjective (Stacks.ModuleStalk.mapFun σ x)) :
    (morphismZeroScheme L L' σ).supportSet ⊆ Z := by
  let : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible
  let : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L' :=
    Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible
  let : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (dualSheaf X.sheaf.obj X.ringCatSheaf.property L) :=
    Invertible.isInvertible_dualSheaf X.sheaf.obj X.ringCatSheaf.property L
  let : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Scheme.tensorDualTwist L L') :=
    tensorProduct_isInvertible X.sheaf.obj X.ringCatSheaf.property L'
      (dualSheaf X.sheaf.obj X.ringCatSheaf.property L)
  let := isInvertible_tensorDualTwist L L'
  let : Stacks.Ample.IsInvertibleModule X L' := ‹_›
  set s : (Scheme.tensorDualTwist L L').sections :=
    sectionsOfTop (Scheme.tensorDualTwist L L') (Scheme.homTensorDualSectionEquiv L L' σ)
  have hs : s.eval (op ⊤) = Scheme.homTensorDualSectionEquiv L L' σ :=
    sectionsOfTop_eval_top _ _
  have hne : s.eval (op ⊤) ≠ 0 := by
    rw [hs]
    exact fun h => hσ ((Scheme.homTensorDualSectionEquiv L L' (X := X)).map_eq_zero_iff.mp h)
  have hloc := nonvanishingLocus_eq_compl_supportSet_zeroScheme (Scheme.tensorDualTwist L L') s hne
  rw [Stacks.NonvanishingSpelling.stalkNonvanishingLocus_eq,
    Stacks.NonvanishingSpelling.sectionsEquiv_apply, hs] at hloc
  intro x hx
  by_contra hxZ
  have hmem := mem_nonvanishingLocus_homTensorDualSection_of_surjective_stalk L L' σ x
    (hoff x hxZ)
  rw [hloc] at hmem
  exact hmem hx

/-- **A nonzero morphism of invertible modules that is a stalkwise epimorphism away from an
integral effective Cartier divisor `D` exhibits the target as the twist of the source by
`D ^ k`.** -/
theorem exists_pow_tensorIso_of_surjective_stalk_off [IsNoetherian X] (D : X.IdealSheafData)
    (hDint : IsIntegral D.subscheme) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    {σ : L ⟶ L'} (hσ : σ ≠ 0)
    (hoff : ∀ x : X, x ∉ D.supportSet → Function.Surjective (Stacks.ModuleStalk.mapFun σ x)) :
    ∃ k : ℕ, Nonempty ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.sheaf.obj,
      Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj) (forget₂ CommRingCat RingCat)
        (X.ringCatSheaf.property)⟩).obj ((Stacks.Divisors.invertibleSheaf' (D ^ k)))).obj (L)) ≅
      L') :=
  exists_pow_tensorIso_of_ne_zero_of_supportSet_subset L L' D hDint hD hσ
    (supportSet_morphismZeroScheme_subset_of_surjective_stalk_off L L' hσ D.supportSet hoff)

end Support

/-! ### The divisor's ideal contains the matrix entries of `σ` -/

section Entries

open Stacks.AlgebraicGeometry.QcohLimits

variable (L L')

/-- The restriction map of the structure sheaf along `U ≤ U` is the identity. -/
private theorem res_self {U : X.Opens} (r : Γ(X, U)) :
    (X.presheaf.map (homOfLE (le_refl U)).op).hom r = r := by simp

/-- Evaluating a section of `SheafHom(L, L')` over `U` at a fixed section of `L` and applying a
linear functional on `Γ(L', U)` is a linear functional on `Γ(SheafHom(L, L'), U)`. -/
def sheafHomFunctional {U : X.Opens} (v : Γ(L, U)) (ψ : Γ(L', U) →ₗ[Γ(X, U)] Γ(X, U)) :
    Γ(sheafHomModule L L', U) →ₗ[Γ(X, U)] Γ(X, U) where
  toFun a := ψ (sheafHomSectionApp L L' le_rfl a v)
  map_add' a b := by
    simp only [sheafHomSectionApp_add]
    exact map_add ψ _ _
  map_smul' r a := by
    simp only [RingHom.id_apply]
    rw [sheafHomSectionApp_smul, res_self, map_smul]

variable [Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] in
/-- The same functional read on the twist `L' ⊗ L^∨` across the comparison
`L' ⊗ L^∨ ≅ SheafHom(L, L')`. -/
def tensorDualFunctional {U : X.Opens} (v : Γ(L, U)) (ψ : Γ(L', U) →ₗ[Γ(X, U)] Γ(X, U)) :
    Γ(Scheme.tensorDualTwist L L', U) →ₗ[Γ(X, U)] Γ(X, U) :=
  (sheafHomFunctional L L' v ψ).comp (appₗ (Scheme.tensorDualIsoSheafHom L L').hom U)

variable [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L']

omit [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L'] in
/-- The value of that functional at the restriction of the section attached to `σ`. -/
theorem tensorDualFunctional_apply (σ : L ⟶ L') {U : X.Opens} (v : Γ(L, U))
    (ψ : Γ(L', U) →ₗ[Γ(X, U)] Γ(X, U)) :
    tensorDualFunctional L L' v ψ
        (((Scheme.tensorDualTwist L L').presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
          (Scheme.homTensorDualSectionEquiv L L' σ))
      = ψ (σ.app U v) := by
  have hnat : (Scheme.tensorDualIsoSheafHom L L').hom.app U
        (((Scheme.tensorDualTwist L L').presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
          (Scheme.homTensorDualSectionEquiv L L' σ))
      = ((sheafHomModule L L').presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
          ((Scheme.tensorDualIsoSheafHom L L').hom.app ⊤
            (Scheme.homTensorDualSectionEquiv L L' σ)) :=
    NatTrans.naturality_apply (F := (Scheme.tensorDualTwist L L').presheaf)
      (G := (sheafHomModule L L').presheaf)
      (Scheme.tensorDualIsoSheafHom L L').hom.mapPresheaf (homOfLE (le_top : U ≤ ⊤)).op
      (Scheme.homTensorDualSectionEquiv L L' σ)
  change ψ (sheafHomSectionApp L L' le_rfl
      ((Scheme.tensorDualIsoSheafHom L L').hom.app U
        (((Scheme.tensorDualTwist L L').presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
          (Scheme.homTensorDualSectionEquiv L L' σ))) v) = _
  rw [hnat, tensorDualIsoSheafHom_homTensorDualSectionEquiv L L' σ]
  exact congrArg ψ ((sheafHomSectionApp_res (le_top : U ≤ ⊤) (le_refl U) _ v).trans
    (sheafHomSectionApp_internalHomSectionsTop σ ((le_refl U).trans le_top) v))

/-- **The ideal of the divisor of `σ` on an affine open contains the value at `σ v` of every
linear functional on the sections of `L'`.** -/
theorem mem_ideal_morphismZeroScheme (σ : L ⟶ L') (U : X.affineOpens) (v : Γ(L, U.1))
    (ψ : Γ(L', U.1) →ₗ[Γ(X, U.1)] Γ(X, U.1)) :
    ψ (σ.app U.1 v) ∈ (morphismZeroScheme L L' σ).ideal U := by
  let : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L' :=
    Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible
  let := isInvertible_tensorDualTwist L L'
  have hz : morphismZeroScheme L L' σ =
      zeroScheme X (Scheme.tensorDualTwist L L') (Scheme.homTensorDualSectionEquiv L L' σ) := rfl
  have hid := zeroScheme_ideal X (Scheme.tensorDualTwist L L')
    (Scheme.homTensorDualSectionEquiv L L' σ) U
  rw [hz, hid]
  exact Ideal.subset_span ⟨tensorDualFunctional L L' v ψ,
    (tensorDualFunctional_apply L L' σ v ψ).symm⟩

end Entries

open Scheme.Modules Stacks.AlgebraicGeometry.ReflexiveModules in
/-- **The determinant comparison map of [Stacks, Tag 0B3T], a stalkwise epimorphism away from an
integral effective Cartier divisor `D`, twists by `D ^ k`.** -/
theorem exists_pow_tensorIso_detMap_of_surjective_stalk_off [IsIntegral X] [IsNoetherian X]
    {F F' : X.Modules} (r : ℤ) (f : F ⟶ F')
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (reflexiveHull (exteriorPower F r))]
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (reflexiveHull (exteriorPower F' r))]
    (D : X.IdealSheafData) (hDint : IsIntegral D.subscheme)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) (hf : detMap f r ≠ 0)
    (hoff : ∀ x : X, x ∉ D.supportSet →
      Function.Surjective (Stacks.ModuleStalk.mapFun (detMap f r) x)) :
    ∃ k : ℕ, Nonempty ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.sheaf.obj,
      Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj) (forget₂ CommRingCat RingCat)
        (X.ringCatSheaf.property)⟩).obj ((Stacks.Divisors.invertibleSheaf' (D ^ k)))).obj
          ((reflexiveHull (exteriorPower F r)))) ≅
      reflexiveHull (exteriorPower F' r)) :=
  exists_pow_tensorIso_of_surjective_stalk_off _ _ D hDint hD hf hoff

end AlgebraicGeometry

end
