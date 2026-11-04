module

public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicCascade.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionIntegral
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeProperties
public import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.Sections

/-!
# A regular global section nonvanishing on a trivializing principal open

Let `X` be an integral quasi-compact quasi-separated scheme, `L` an invertible `𝒪_X`-module,
`f` a global function, and suppose `L` is trivial on the principal open `D(f) = X_f`. Then `L`
has a nonzerodivisor global section whose zero scheme misses `D(f)` entirely: the generator of
`L` over `D(f)` provided by the trivialization is, after multiplication by a power of `f`, the
restriction of a global section, and multiplying by a power of `f` does not change where the
section generates, because `f` is invertible on `D(f)`.

This is the mechanism by which an invertible module trivial on an open subscheme is exhibited as
`𝒪_X(D)` for an effective Cartier divisor `D` supported in the closed complement: the divisor is
the zero scheme of the section produced here.

## Main definitions

* `AlgebraicGeometry.overCoordinate` — the coordinate of a section over an open contained in the
  trivializing one, read off a trivialization of the module *over* that open.

## Main results

* `AlgebraicGeometry.nonempty_overIso_of_nonempty_pullbackIso` — a trivialization of the
  restriction `L|_U` gives a trivialization of `L` over `U` in the slice category, which is the
  form that evaluates on every open contained in `U`.
* `AlgebraicGeometry.overCoordinate_restrict` — the coordinate is compatible with restriction.
* `AlgebraicGeometry.notMem_zeroScheme_support_of_isUnit_overCoordinate` — a global section whose
  coordinate on the trivializing open is a unit vanishes nowhere there.
* `AlgebraicGeometry.exists_restriction_eq_pow_smul` — a section over a principal open is a
  power of the function times the restriction of a section over the ambient open.
* `AlgebraicGeometry.exists_isRegularSection_zeroScheme_disjoint_basicOpen` — the main result.

## Implementation notes

**Why the slice category.** A trivialization is given as an isomorphism `L|_U ≅ 𝒪_U` of modules
on the open subscheme `U`, but the zero scheme of a section is computed from the coordinate of
that section on *affine* opens `V ⊆ U` of `X`. The module `L.over U` on the slice site has an
object for every such `V`, and `AlgebraicGeometry.Scheme.Modules.overEquiv` identifies modules on
the slice site with modules on `U`; so transporting the trivialization across that equivalence
turns it into a coordinate on every `V ≤ U` at once, compatibly with restriction.

**Where the power of `f` comes from.**
`AlgebraicGeometry.isLocalizedModule_restriction_basicOpen_of_qcqs` says that the sections of a
quasi-coherent module over `D(f)` are the localization away from `f` of its sections over the
ambient open — this is [Stacks, Tag 01PW] for an invertible, hence quasi-coherent, module. So the
generator over `D(f)` becomes `f^{-n}` times the restriction of a global section, and that global
section is the one wanted.

**Why regularity is not proved here.** On an integral scheme a nonzero global section of an
invertible module is already a nonzerodivisor, which is
`AlgebraicGeometry.isRegularSection_of_eval_top_ne_zero`; the section constructed here is nonzero
because its coordinate on the nonempty open `D(f)` is a unit and the functions there form a
nontrivial ring.

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01WY](https://stacks.math.columbia.edu/tag/01WY)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### Trivializing an invertible module over an open -/

/-- **A trivialization of `L|_U` is a trivialization of `L` over `U`.** The equivalence
`AlgebraicGeometry.Scheme.Modules.overEquiv` identifies modules on the slice site of `U` with
modules on the open subscheme `U`, and carries `L.over U` to `L|_U`. -/
theorem nonempty_overIso_of_nonempty_pullbackIso (U : X.Opens) (L : X.Modules)
    (h : Nonempty ((Scheme.Modules.pullback U.ι).obj L ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf)) :
    Nonempty (L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) := by
  obtain ⟨e⟩ := h
  refine ⟨(Scheme.Modules.overEquiv U).fullyFaithfulFunctor.preimageIso ?_⟩
  exact (Scheme.Modules.overFunctorEquiv U).app L ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).app L ≪≫ e ≪≫
    (Scheme.Modules.restrictUnitIso U.ι).symm ≪≫
    ((Scheme.Modules.overFunctorEquiv U).app (SheafOfModules.unit X.ringCatSheaf)).symm

/-- **The coordinate of a section against a trivialization over an open.** For an open `V`
contained in the trivializing open `U`, evaluating the trivialization at `V` identifies the
sections of `L` over `V` with the functions on `V`. -/
def overCoordinate {L : X.Modules} {U : X.Opens}
    (e : L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    {V : X.Opens} (hVU : V ≤ U) : Γ(L, V) ≃ₗ[Γ(X, V)] Γ(X, V) :=
  ((SheafOfModules.evaluation (X.ringCatSheaf.over U)
    (op (Over.mk (homOfLE hVU)))).mapIso e).toLinearEquiv

/-- The coordinate against a trivialization commutes with restriction to a smaller open. -/
theorem overCoordinate_restrict {L : X.Modules} {U : X.Opens}
    (e : L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    {V W : X.Opens} (hVU : V ≤ U) (hWV : W ≤ V) (t : Γ(L, V)) :
    overCoordinate e (hWV.trans hVU) (L.presheaf.map (homOfLE hWV).op t) =
      X.presheaf.map (homOfLE hWV).op (overCoordinate e hVU t) :=
  congrArg (fun φ => φ t)
    (e.hom.val.naturality (Over.homMk (homOfLE hWV) :
      Over.mk (homOfLE (hWV.trans hVU)) ⟶ Over.mk (homOfLE hVU)).op)

/-- Restriction of a global section of a module on a scheme, in the `eval` spelling. -/
theorem sections_eval_restrict {L : X.Modules} (s : L.sections) {V W : X.Opens} (h : W ≤ V) :
    L.presheaf.map (homOfLE h).op (s.eval (op V)) = s.eval (op W) :=
  PresheafOfModules.sections_property s (homOfLE h).op

/-- The coordinate of a global section on an open contained in the trivializing one is the
restriction of its coordinate there. -/
theorem overCoordinate_eval {L : X.Modules} {U : X.Opens}
    (e : L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (s : L.sections) {V : X.Opens} (hVU : V ≤ U) :
    overCoordinate e hVU (s.eval (op V)) =
      X.presheaf.map (homOfLE hVU).op (overCoordinate e le_rfl (s.eval (op U))) := by
  rw [← sections_eval_restrict s hVU]
  exact overCoordinate_restrict e le_rfl hVU (s.eval (op U))

/-- **A global section whose coordinate on a trivializing open is a unit vanishes nowhere on
that open.** On an affine open `V ⊆ U` the ideal of the zero scheme is generated by the
coordinate there, which is a unit, so the ideal is the whole ring and its zero locus is
empty. -/
theorem notMem_zeroScheme_support_of_isUnit_overCoordinate
    {L : X.Modules}
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] {U : X.Opens}
    (e : L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (s : L.sections) (hs : IsUnit (overCoordinate e le_rfl (s.eval (op U))))
    {x : X} (hx : x ∈ U) :
    x ∉ (zeroScheme X L (s.eval (op ⊤))).support := by
  obtain ⟨-, ⟨V, hV, rfl⟩, hxV, hsub⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  have hVU : V ≤ U := hsub
  have he : IsUnit (overCoordinate e hVU (s.eval (op V))) := by
    rw [overCoordinate_eval e s hVU]
    exact hs.map (X.presheaf.map (homOfLE hVU).op).hom
  intro hzero
  have hz := (Scheme.IdealSheafData.mem_supportSet_iff_of_mem (U := ⟨V, hV⟩) hxV).mp hzero
  have hideal : (zeroScheme X L (s.eval (op ⊤))).ideal ⟨V, hV⟩ =
      Ideal.span {overCoordinate e hVU (s.eval (op V))} := by
    refine zeroScheme_ideal_of_trivialization X L (s.eval (op ⊤)) ⟨V, hV⟩
      (overCoordinate e hVU) _ ?_
    exact congrArg (overCoordinate e hVU) (sections_eval_restrict s (le_top : V ≤ ⊤))
  have hitop : (zeroScheme X L (s.eval (op ⊤))).ideal ⟨V, hV⟩ = ⊤ := by
    rw [hideal, Ideal.span_singleton_eq_top]
    exact he
  rw [hitop] at hz
  have hn := (Scheme.mem_zeroLocus_iff X (U := V) ((⊤ : Ideal Γ(X, V)) : Set Γ(X, V)) x).mp hz
    1 (by simp)
  exact hn (by rw [Scheme.basicOpen_one]; exact hxV)

/-! ### The main construction -/

/-- **A section over a principal open becomes, after multiplication by a power of the function, a
restriction of a section over the ambient open.** This is [Stacks, Tag 01PW] for a quasi-coherent
module on a quasi-compact quasi-separated open. -/
theorem exists_restriction_eq_pow_smul
    (L : X.Modules) [SheafOfModules.IsQuasicoherent L]
    {U : X.Opens} (hU : IsCompact (U : Set X)) (hUqs : IsQuasiSeparated (U : Set X))
    (f : Γ(X, U)) (s : Γ(L, X.basicOpen f)) :
    ∃ (n : ℕ) (t : Γ(L, U)),
      L.presheaf.map (homOfLE (X.basicOpen_le f)).op t =
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) ^ n • s := by
  let : Module Γ(X, U) Γ(L, X.basicOpen f) :=
    Module.compHom Γ(L, X.basicOpen f)
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
  let : IsLocalizedModule.Away f
      (Scheme.Modules.restrictionLinearMap L (homOfLE (X.basicOpen_le f))) :=
    isLocalizedModule_restriction_basicOpen_of_qcqs L hU hUqs f
  obtain ⟨n, t, ht⟩ := IsLocalizedModule.Away.surj
    (Scheme.Modules.restrictionLinearMap L (homOfLE (X.basicOpen_le f))) f s
  refine ⟨n, t, ?_⟩
  change (X.presheaf.map (homOfLE (X.basicOpen_le f)).op) (f ^ n) • s =
    L.presheaf.map (homOfLE (X.basicOpen_le f)).op t at ht
  rw [map_pow] at ht
  exact ht.symm

/-- **An invertible module trivial on a nonempty principal open of an integral quasi-compact
quasi-separated scheme has a nonzerodivisor global section vanishing nowhere on that open.** The
trivialization gives a generator over `D(f)`; a power of `f` times it extends to a global
section, which is still a unit in the trivialization because `f` is invertible on `D(f)`, and a
nonzero global section of an invertible module on an integral scheme is a nonzerodivisor. -/
theorem exists_isRegularSection_zeroScheme_disjoint_basicOpen
    [IsIntegral X] [CompactSpace X] [QuasiSeparatedSpace X]
    (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (f : Γ(X, (⊤ : X.Opens))) (hU : (X.basicOpen f : Set X).Nonempty)
    (e : L.over (X.basicOpen f) ≅ SheafOfModules.unit (X.ringCatSheaf.over (X.basicOpen f))) :
    ∃ s : L.sections,
      IsRegularSection X.sheaf.obj X.ringCatSheaf.property s ∧
      ∀ x ∈ X.basicOpen f, x ∉ (zeroScheme X L (s.eval (op ⊤))).support := by
  obtain ⟨n, t, ht⟩ := exists_restriction_eq_pow_smul L
    (by simpa using isCompact_univ (X := X))
    (by simpa using (isQuasiSeparated_univ : IsQuasiSeparated (Set.univ : Set X))) f
    ((overCoordinate e le_rfl).symm 1)
  set s : L.sections := Stacks.Divisors.sectionsOfTop L t with hsdef
  have hcoord : IsUnit (overCoordinate e le_rfl (s.eval (op (X.basicOpen f)))) := by
    have hres : s.eval (op (X.basicOpen f)) =
        L.presheaf.map (homOfLE (X.basicOpen_le f)).op t :=
      Stacks.Divisors.sectionsOfTop_eval L t (X.basicOpen f)
    rw [hres, ht, map_smul]
    simp only [LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
    exact (X.toRingedSpace.isUnit_res_basicOpen f).pow n
  obtain ⟨x₀, hx₀⟩ := hU
  have : Nonempty (X.basicOpen f) := ⟨⟨x₀, hx₀⟩⟩
  have : Nontrivial Γ(X, X.basicOpen f) := Scheme.component_nontrivial X (X.basicOpen f)
  have hne : s.eval (op (⊤ : X.Opens)) ≠ 0 := by
    intro h0
    have hzero : s.eval (op (X.basicOpen f)) = 0 := by
      rw [← sections_eval_restrict s (X.basicOpen_le f), h0]
      exact map_zero _
    have hzero' : overCoordinate e le_rfl (s.eval (op (X.basicOpen f))) = 0 := by
      rw [hzero]
      exact (overCoordinate e le_rfl).map_zero
    rw [hzero'] at hcoord
    exact not_isUnit_zero hcoord
  exact ⟨s, isRegularSection_of_eval_top_ne_zero L s hne,
    fun x hx => notMem_zeroScheme_support_of_isUnit_overCoordinate e s hcoord hx⟩

end AlgebraicGeometry

end
