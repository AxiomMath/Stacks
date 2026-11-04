module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsBridge
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalFormalSections.Algebraization
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsSerreOneAlternative

/-!
# The comparison map of Stacks 0EIH in its sheaf-theoretic spelling

[Stacks, Tag 0EIH] is proved in `Stacks.Algebraization.FormalSections.isIso_formalComparison` for
the explicitly constructed map

`colim_{V} Γ(V, M̃) ⟶ lim_n Γ(U, (M/fⁿM)̃)`

of `Stacks.Algebraization.FormalSections.formalComparison`, whose two sides are built from the
locally fractional sections `Stacks.LocalCohomology.moduleSections` of an `A`-module. The
comparison map of [Stacks, Tag 0EG2] on `U = Spec(A) ∖ V(𝔞)`, which is the one the algebraization
statements above [Stacks, Tag 0EIH] consume, is instead
`Stacks.Algebraization.principalComparisonMap`: it compares the colimit of the sections of the
sheaf `M̃|_U` over the neighbourhoods of `U ∩ V(f)` with the limit of the sections of the sheaf
quotients `(M̃|_U) / (f)ⁿ (M̃|_U)`.

This file identifies the second map's target with the first's and concludes that the second map is
an isomorphism too, so that [Stacks, Tag 0EIH] becomes available in the vocabulary of
[Stacks, Tag 0EG2].

## The identification

The sections of `M̃|_U` over an open `W` of `U` *are* the locally fractional sections of `M` over
the image of `W` in `Spec(A)`: `Stacks.LocalCohomology.complementTilde` is the pushforward of the
sheafification along the open immersion, so the two agree by definition. The `n`-th sheaf quotient
is `(M/fⁿM)̃|_U` by `Stacks.Algebraization.quotIso`, so its sections over `W` are the locally
fractional sections of `M/fⁿM` over the image of `W`.

That turns a compatible family of sections of the sheaf quotients on `U` into a point of
`Stacks.Algebraization.FormalSections.formalLimit`, injectively, and turns a section of `M̃` over a
neighbourhood of `U ∩ V(f)` in the first model into one in the second. [Stacks, Tag 0EIH] supplies
a neighbourhood realizing the image family, and that neighbourhood realizes the original family
because the translation is injective; realization on one neighbourhood is exactly surjectivity of
the comparison map (`Stacks.Algebraization.isIso_comparisonMap_iff_realized`), and injectivity of
the comparison map is unconditional
(`Stacks.Algebraization.mono_principalComparisonMap`).

## Main results

* `Stacks.Algebraization.quotModuleIso` — the two spellings `M / (f)ⁿ M` and `M / fⁿM` of the
  `n`-th quotient of the tower agree.
* `Stacks.Algebraization.isIso_principalComparisonMap` — **[Stacks, Tag 0EIH] for the comparison
  map of [Stacks, Tag 0EG2]**.

## Implementation notes

The level-zero term of both towers is the zero module, and the naturality of the identification is
available from `Stacks.Algebraization.quotIso_naturality` only for the transitions between levels
`≥ 1`. The translation of a compatible family therefore reads its level-zero component off level
one through the transition map, as
`Stacks.Algebraization.isIso_globalSectionsToLimit_coherentPrincipalTilde` does; nothing is lost,
because the level-zero component of a compatible family is determined by the level-one one.

`Stacks.Algebraization.complementTilde A a M` and
`(Stacks.Algebraization.principalTildeFunctor hf).obj M` are the same sheaf by definition, but
unifying them is expensive, so everything below is stated in the second spelling, which is the one
`quotIso` uses; the single crossing to the first is in the final theorem.

The ideal sheaves `Stacks.Algebraization.idealSheafNearVanishing A (f) 𝔞` and
`Stacks.Algebraization.principalIdealOnOpen hf` are equal but not definitionally so, and rewriting
the equality inside an ideal-power quotient does not terminate; the equality is therefore consumed
by `subst` on a universally quantified ideal sheaf.

## References

* [Stacks Project, Tag 0EIH](https://stacks.math.columbia.edu/tag/0EIH)
* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.LocalCohomology

noncomputable section

universe u

namespace Stacks.Algebraization

open Stacks.Algebraization.FormalSections

variable {A : Type u} [CommRing A] {a : Ideal A} {f : A}

/-! ### The two spellings of `M / fⁿ M` -/

/-- `fⁿ M` is `(f)ⁿ M`: the multiples of `fⁿ` are the `(f)ⁿ`-multiples. -/
public theorem powSmul_eq_pow_smul_top (f : A) (M : ModuleCat.{u} A) (n : ℕ) :
    powSmul f M n = (Ideal.span {f}) ^ n • (⊤ : Submodule A (M : Type u)) := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
  ext x
  simp only [mem_powSmul, Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]

/-- **The two spellings of the `n`-th term of the tower agree**: the quotient of `M` by the
`(f)ⁿ`-multiples is the quotient by the `fⁿ`-multiples. -/
public def quotModuleIso (f : A) (M : ModuleCat.{u} A) (n : ℕ) :
    ComplementTower.quotientModule A f M n ≅ Quot f M n :=
  (Submodule.quotEquivOfEq _ _ (powSmul_eq_pow_smul_top f M n).symm).toModuleIso

/-- `quotModuleIso` intertwines the two quotient projections. -/
public theorem quotientMap_comp_quotModuleIso (f : A) (M : ModuleCat.{u} A) (n : ℕ) :
    ComplementTower.quotientMap A f M n ≫ (quotModuleIso f M n).hom = quotMk f M n :=
  ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

/-- `quotModuleIso` intertwines the two transition maps. -/
public theorem quotModuleIso_comp_quotLe (f : A) (M : ModuleCat.{u} A) (n : ℕ) :
    (quotModuleIso f M (n + 1)).hom ≫ quotLe f M (Nat.le_succ n) =
      ComplementTower.quotientTransition A f M n ≫ (quotModuleIso f M n).hom :=
  ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl))

/-! ### The sheaf terms of the tower -/

section Noetherian

variable [IsNoetherianRing A]

/-- **The `n`-th sheaf quotient `(M̃|_U) / (f)ⁿ (M̃|_U)` is `(M/fⁿM)̃|_U`**, compatibly with the
quotient projections and with the transitions between consecutive levels.

The identification is `Stacks.Algebraization.quotIso` followed by the sheafification of
`Stacks.Algebraization.quotModuleIso`; its two compatibilities are `quotIso_spec` and
`quotIso_naturality`. -/
public theorem exists_principalTermIso (hf : f ∈ a) (M : ModuleCat.{u} A) :
    ∃ e : ∀ n : ℕ, idealPowerQuotient (idealSheafNearVanishing A (Ideal.span {f}) a) n
          ((principalTildeFunctor hf).obj M) ≅ (principalTildeFunctor hf).obj (Quot f M n),
      (∀ n : ℕ, cokernel.π (idealPowerMultiple (idealSheafNearVanishing A (Ideal.span {f}) a) n
            ((principalTildeFunctor hf).obj M)).ι ≫ (e n).hom =
          (principalTildeFunctor hf).map (quotMk f M n)) ∧
        ∀ n : ℕ, (adicQuotientSystem (idealSheafNearVanishing A (Ideal.span {f}) a)
              ((principalTildeFunctor hf).obj M)).map (homOfLE (Nat.le_succ (n + 1))).op ≫
              (e (n + 1)).hom =
            (e (n + 2)).hom ≫
              (principalTildeFunctor hf).map (quotLe f M (Nat.le_succ (n + 1))) := by
  suffices h : ∀ J : (complementZeroLocus A a : Scheme).IdealSheafData,
      J = principalIdealOnOpen hf →
      ∃ e : ∀ n : ℕ, idealPowerQuotient J n ((principalTildeFunctor hf).obj M) ≅
            (principalTildeFunctor hf).obj (Quot f M n),
        (∀ n : ℕ, cokernel.π (idealPowerMultiple J n
              ((principalTildeFunctor hf).obj M)).ι ≫ (e n).hom =
            (principalTildeFunctor hf).map (quotMk f M n)) ∧
          ∀ n : ℕ, (adicQuotientSystem J ((principalTildeFunctor hf).obj M)).map
                (homOfLE (Nat.le_succ (n + 1))).op ≫ (e (n + 1)).hom =
              (e (n + 2)).hom ≫
                (principalTildeFunctor hf).map (quotLe f M (Nat.le_succ (n + 1))) by
    exact h _ ((idealSheafNearVanishing_span_singleton A a f).trans
      (principalIdealOnOpen_eq hf).symm)
  intro J hJ
  subst hJ
  refine ⟨fun n => quotIso hf M n ≪≫ (principalTildeFunctor hf).mapIso (quotModuleIso f M n),
    fun n => ?_, fun n => ?_⟩
  · exact (Category.assoc (obj := (complementZeroLocus A a : Scheme).Modules) _ _ _).symm.trans
      ((congrArg (fun k => k ≫ (principalTildeFunctor hf).map (quotModuleIso f M n).hom)
          (quotIso_spec hf M n)).trans
        (((principalTildeFunctor hf).map_comp _ _).symm.trans
          (congrArg (principalTildeFunctor hf).map (quotientMap_comp_quotModuleIso f M n))))
  · refine (Category.assoc (obj := (complementZeroLocus A a : Scheme).Modules) _ _ _).symm.trans ?_
    refine ((congrArg (fun k => k ≫ (principalTildeFunctor hf).map (quotModuleIso f M (n + 1)).hom)
      (quotIso_naturality hf M n)).trans ?_)
    refine (Category.assoc (obj := (complementZeroLocus A a : Scheme).Modules) _ _ _).trans ?_
    refine (congrArg (fun k => (quotIso hf M (n + 2)).hom ≫ k)
      (((principalTildeFunctor hf).map_comp _ _).symm)).trans ?_
    refine Eq.trans ?_
      (Category.assoc (obj := (complementZeroLocus A a : Scheme).Modules) _ _ _).symm
    refine congrArg (fun k => (quotIso hf M (n + 2)).hom ≫ k) ?_
    refine Eq.trans ?_ ((principalTildeFunctor hf).map_comp _ _)
    exact congrArg (principalTildeFunctor hf).map (quotModuleIso_comp_quotLe f M (n + 1)).symm

/-! ### Translating a formal section into the concrete model -/

/-- The chosen identification of `(M̃|_U) / (f)ⁿ (M̃|_U)` with `(M/fⁿM)̃|_U`. -/
public def principalTermIso (hf : f ∈ a) (M : ModuleCat.{u} A) (n : ℕ) :
    idealPowerQuotient (idealSheafNearVanishing A (Ideal.span {f}) a) n
        ((principalTildeFunctor hf).obj M) ≅ (principalTildeFunctor hf).obj (Quot f M n) :=
  (exists_principalTermIso hf M).choose n

/-- `principalTermIso` intertwines the quotient projections. -/
public theorem cokernel_π_comp_principalTermIso (hf : f ∈ a) (M : ModuleCat.{u} A) (n : ℕ) :
    cokernel.π (idealPowerMultiple (idealSheafNearVanishing A (Ideal.span {f}) a) n
        ((principalTildeFunctor hf).obj M)).ι ≫ (principalTermIso hf M n).hom =
      (principalTildeFunctor hf).map (quotMk f M n) :=
  (exists_principalTermIso hf M).choose_spec.1 n

/-- `principalTermIso` intertwines the transitions of the two towers. -/
public theorem principalTermIso_naturality (hf : f ∈ a) (M : ModuleCat.{u} A) (n : ℕ) :
    (adicQuotientSystem (idealSheafNearVanishing A (Ideal.span {f}) a)
          ((principalTildeFunctor hf).obj M)).map (homOfLE (Nat.le_succ (n + 1))).op ≫
        (principalTermIso hf M (n + 1)).hom =
      (principalTermIso hf M (n + 2)).hom ≫
        (principalTildeFunctor hf).map (quotLe f M (Nat.le_succ (n + 1))) :=
  (exists_principalTermIso hf M).choose_spec.2 n

omit [IsNoetherianRing A] in
/-- Applying a composite of morphisms of `𝒪_U`-modules to a section applies the two factors in
turn. -/
public theorem hom_app_comp_apply {F G H : (complementZeroLocus A a : Scheme).Modules}
    (φ : F ⟶ G) (ψ : G ⟶ H) (W : (complementZeroLocus A a : Scheme).Opens)
    (x : ToType (Γ(F, W))) :
    Scheme.Modules.Hom.app (φ ≫ ψ) W x =
      Scheme.Modules.Hom.app ψ W (Scheme.Modules.Hom.app φ W x) := rfl

/-- **A module map acts on the sections of the sheaves it induces on `U` by acting on
numerators.** The sections of `Ñ|_U` over an open `W` of `U` are the locally fractional sections
of `N` over the image of `W` in `Spec(A)`, and the induced map of sheaves acts as
`Stacks.LocalCohomology.moduleSectionsMap`. -/
public theorem hom_app_principalTildeFunctor_map (hf : f ∈ a) {N N' : ModuleCat.{u} A}
    (φ : N ⟶ N') (W : (complementZeroLocus A a : Scheme).Opens)
    (x : ToType (Γ((principalTildeFunctor hf).obj N, W))) :
    Scheme.Modules.Hom.app ((principalTildeFunctor hf).map φ) W x =
      moduleSectionsMap φ ((complementZeroLocus A a).ι ''ᵁ W) x := rfl

/-- The `n`-th component of a formal section of `M̃|_U`, read as a locally fractional section of
`M / fⁿM` on `U`. -/
public def formalLevel (hf : f ∈ a) (M : ModuleCat.{u} A) (n : ℕ)
    (s : ToType (limit (formalSections A (Ideal.span {f}) a
      ((principalTildeFunctor hf).obj M)))) :
    moduleSections (Quot f M n) (complOpen A a) :=
  moduleSectionsRestrict (Quot f M n)
    (Scheme.Opens.ι_image_top (complementZeroLocus A a)).ge
    (Scheme.Modules.Hom.app (principalTermIso hf M n).hom ⊤
      (ConcreteCategory.hom (limit.π (formalSections A (Ideal.span {f}) a
        ((principalTildeFunctor hf).obj M)) (op n)) s))

/-- The level maps are injective: `principalTermIso` is an isomorphism of sheaves, so it is
bijective on sections, and restriction along an equality of opens is an equivalence. -/
public theorem formalLevel_injective (hf : f ∈ a) (M : ModuleCat.{u} A) (n : ℕ)
    {s t : ToType (limit (formalSections A (Ideal.span {f}) a
      ((principalTildeFunctor hf).obj M)))}
    (h : formalLevel hf M n s = formalLevel hf M n t) :
    ConcreteCategory.hom (limit.π (formalSections A (Ideal.span {f}) a
        ((principalTildeFunctor hf).obj M)) (op n)) s =
      ConcreteCategory.hom (limit.π (formalSections A (Ideal.span {f}) a
        ((principalTildeFunctor hf).obj M)) (op n)) t := by
  have hbij : Function.Bijective
      (Scheme.Modules.Hom.app (principalTermIso hf M n).hom
        (⊤ : (complementZeroLocus A a : Scheme).Opens)) :=
    ConcreteCategory.bijective_of_isIso
      (((Scheme.Modules.toPresheaf (complementZeroLocus A a : Scheme) ⋙
        (CategoryTheory.evaluation _ Ab.{u}).obj (op ⊤)).mapIso (principalTermIso hf M n)).hom)
  exact hbij.1 ((moduleSectionsCongr (Quot f M n)
    (Scheme.Opens.ι_image_top (complementZeroLocus A a))).injective h)

/-- The level maps are compatible with the transitions of the tower of quotients. -/
public theorem formalLevel_transition (hf : f ∈ a) (M : ModuleCat.{u} A) (n : ℕ)
    (s : ToType (limit (formalSections A (Ideal.span {f}) a
      ((principalTildeFunctor hf).obj M)))) :
    moduleSectionsMap (quotLe f M (Nat.le_succ (n + 1))) (complOpen A a)
        (formalLevel hf M (n + 2) s) =
      formalLevel hf M (n + 1) s :=
  have hnat0 := congrArg (fun k => Scheme.Modules.Hom.app k
      (⊤ : (complementZeroLocus A a : Scheme).Opens)) (principalTermIso_naturality hf M n)
  have hnat := ConcreteCategory.congr_hom hnat0
    (ConcreteCategory.hom (limit.π (formalSections A (Ideal.span {f}) a
      ((principalTildeFunctor hf).obj M)) (op (n + 2))) s)
  have hnatL := hom_app_comp_apply
    ((adicQuotientSystem (idealSheafNearVanishing A (Ideal.span {f}) a)
      ((principalTildeFunctor hf).obj M)).map (homOfLE (Nat.le_succ (n + 1))).op)
    (principalTermIso hf M (n + 1)).hom ⊤
    (ConcreteCategory.hom (limit.π (formalSections A (Ideal.span {f}) a
      ((principalTildeFunctor hf).obj M)) (op (n + 2))) s)
  have hnatR := hom_app_comp_apply (principalTermIso hf M (n + 2)).hom
    ((principalTildeFunctor hf).map (quotLe f M (Nat.le_succ (n + 1)))) ⊤
    (ConcreteCategory.hom (limit.π (formalSections A (Ideal.span {f}) a
      ((principalTildeFunctor hf).obj M)) (op (n + 2))) s)
  have hw := limit.w_apply (formalSections A (Ideal.span {f}) a ((principalTildeFunctor hf).obj M))
    (homOfLE (Nat.le_succ (n + 1))).op s
  have hinner := (hom_app_principalTildeFunctor_map hf (quotLe f M (Nat.le_succ (n + 1)))
      (⊤ : (complementZeroLocus A a : Scheme).Opens)
      (Scheme.Modules.Hom.app (principalTermIso hf M (n + 2)).hom ⊤
        (ConcreteCategory.hom (limit.π (formalSections A (Ideal.span {f}) a
          ((principalTildeFunctor hf).obj M)) (op (n + 2))) s))).symm.trans
    ((hnatR.symm.trans (hnat.symm.trans hnatL)).trans
      (congrArg (Scheme.Modules.Hom.app (principalTermIso hf M (n + 1)).hom ⊤) hw))
  (moduleSectionsMap_restrict (quotLe f M (Nat.le_succ (n + 1)))
      (Scheme.Opens.ι_image_top (complementZeroLocus A a)).ge
      (Scheme.Modules.Hom.app (principalTermIso hf M (n + 2)).hom ⊤
        (ConcreteCategory.hom (limit.π (formalSections A (Ideal.span {f}) a
          ((principalTildeFunctor hf).obj M)) (op (n + 2))) s))).trans
    (congrArg (moduleSectionsRestrict (Quot f M (n + 1))
      (Scheme.Opens.ι_image_top (complementZeroLocus A a)).ge) hinner)

/-- A formal section of `M̃|_U`, read as a point of
`Stacks.Algebraization.FormalSections.formalLimit`. The level-zero component is read off level one
through the transition map, the two towers being compatible only from level one on. -/
public def toFormalLimitOfSection (hf : f ∈ a) (M : ModuleCat.{u} A)
    (s : ToType (limit (formalSections A (Ideal.span {f}) a
      ((principalTildeFunctor hf).obj M)))) :
    formalLimit f M (complOpen A a) :=
  ⟨fun n => match n with
    | 0 => moduleSectionsMap (quotLe f M (Nat.le_succ 0)) (complOpen A a) (formalLevel hf M 1 s)
    | (k + 1) => formalLevel hf M (k + 1) s,
   by
     intro n
     cases n with
     | zero => rfl
     | succ k => exact formalLevel_transition hf M k s⟩

/-- The components of the translation above level zero. -/
@[simp] public theorem toFormalLimitOfSection_succ (hf : f ∈ a) (M : ModuleCat.{u} A)
    (s : ToType (limit (formalSections A (Ideal.span {f}) a
      ((principalTildeFunctor hf).obj M)))) (k : ℕ) :
    (toFormalLimitOfSection hf M s).1 (k + 1) = formalLevel hf M (k + 1) s := rfl

/-- **The translation of a formal section is injective.** -/
public theorem toFormalLimitOfSection_injective (hf : f ∈ a) (M : ModuleCat.{u} A)
    {s t : ToType (limit (formalSections A (Ideal.span {f}) a
      ((principalTildeFunctor hf).obj M)))}
    (h : toFormalLimitOfSection hf M s = toFormalLimitOfSection hf M t) : s = t := by
  have hlevel : ∀ k : ℕ, formalLevel hf M (k + 1) s = formalLevel hf M (k + 1) t := fun k =>
    (toFormalLimitOfSection_succ hf M s k).symm.trans
      ((congrArg (fun z : formalLimit f M (complOpen A a) => z.1 (k + 1)) h).trans
        (toFormalLimitOfSection_succ hf M t k))
  refine Limits.Concrete.limit_ext
    (formalSections A (Ideal.span {f}) a ((principalTildeFunctor hf).obj M)) s t fun n => ?_
  obtain ⟨m⟩ := n
  cases m with
  | succ k => exact formalLevel_injective hf M (k + 1) (hlevel k)
  | zero =>
    have hw := limit.w_apply (formalSections A (Ideal.span {f}) a
      ((principalTildeFunctor hf).obj M)) (homOfLE (Nat.le_succ 0)).op
    exact (hw s).symm.trans ((congrArg
      (ConcreteCategory.hom ((formalSections A (Ideal.span {f}) a
        ((principalTildeFunctor hf).obj M)).map (homOfLE (Nat.le_succ 0)).op))
      (formalLevel_injective hf M 1 (hlevel 0))).trans (hw t))

/-! ### Translating a neighbourhood of the formal locus -/

omit [IsNoetherianRing A] in
/-- A morphism of `𝒪_U`-modules commutes with restriction of sections. -/
public theorem hom_app_naturality {F G : (complementZeroLocus A a : Scheme).Modules} (φ : F ⟶ G)
    {W W' : (complementZeroLocus A a : Scheme).Opens} (h : W' ≤ W) (x : ToType (Γ(F, W))) :
    Scheme.Modules.Hom.app φ W' (F.presheaf.map (homOfLE h).op x) =
      G.presheaf.map (homOfLE h).op (Scheme.Modules.Hom.app φ W x) :=
  PresheafOfModules.naturality_apply φ.val (homOfLE h).op x

omit [IsNoetherianRing A] in
/-- An open of `Spec(A)` inside `U` is the image of its preimage in `U`. -/
public theorem image_preimage_of_le_complementZeroLocus
    {W : (Spec (CommRingCat.of A)).Opens} (hW : W ≤ complementZeroLocus A a) :
    (complementZeroLocus A a).ι ''ᵁ ((complementZeroLocus A a).ι ⁻¹ᵁ W) = W := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.2 hW

/-- A neighbourhood of the formal locus in the model of
`Stacks.Algebraization.FormalSections.OpenNearVanishing`, read as one in the model of
`Stacks.Algebraization.OpensNearVanishing`: its preimage in `U`. -/
public def toOpensNearVanishing (V : OpenNearVanishing A a f) :
    OpensNearVanishing A (Ideal.span {f}) a where
  openSet := (complementZeroLocus A a).ι ⁻¹ᵁ V.carrier
  contains_vanishing := by
    intro x hx
    exact V.vanishing_le x.1 x.2 ((Ideal.span_singleton_le_iff_mem _).1 hx)

omit [IsNoetherianRing A] in
/-- The image in `Spec(A)` of the translated neighbourhood is the original open. -/
public theorem image_toOpensNearVanishing (V : OpenNearVanishing A a f) :
    (complementZeroLocus A a).ι ''ᵁ (toOpensNearVanishing V).openSet = V.carrier :=
  image_preimage_of_le_complementZeroLocus V.le_complement

/-- A section of `M̃` on a neighbourhood of the formal locus, read as a section of `M̃|_U` on the
translated neighbourhood. -/
public def toSectionNearVanishing (hf : f ∈ a) (M : ModuleCat.{u} A) (V : OpenNearVanishing A a f)
    (t : moduleSections M V.carrier) :
    ToType ((sectionsNearVanishing A (Ideal.span {f}) a
      ((principalTildeFunctor hf).obj M)).obj (toOpensNearVanishing V)) :=
  moduleSectionsCongr M (image_toOpensNearVanishing V).symm t

omit [IsNoetherianRing A] in
/-- Transporting a section along an equality of opens and back leaves it unchanged. -/
public theorem moduleSectionsCongr_congr_symm {N : ModuleCat.{u} A}
    {U V : Opens (PrimeSpectrum.Top A)} (h : U = V) (t : moduleSections N V) :
    moduleSectionsCongr N h (moduleSectionsCongr N h.symm t) = t := rfl

/-- **The comparison of [Stacks, Tag 0EG2] at a translated neighbourhood is the concrete one.**
Level by level, the translation of the comparison at the neighbourhood `V` of a section `t` of
`M̃` on `V` is the reduction of `t` modulo `fⁿ` extended back to `U`. -/
public theorem formalLevel_comparisonAt (hf : f ∈ a) (M : ModuleCat.{u} A) (n : ℕ)
    (V : OpenNearVanishing A a f) (t : moduleSections M V.carrier) :
    formalLevel hf M n (ConcreteCategory.hom (comparisonAt A (Ideal.span {f}) a
        ((principalTildeFunctor hf).obj M) (toOpensNearVanishing V))
      (toSectionNearVanishing hf M V t)) =
      extendQuot A a f M V n (moduleSectionsMap (quotMk f M n) V.carrier t) := by
  have hπ := ConcreteCategory.congr_hom (comparisonAt_π A (Ideal.span {f}) a
      ((principalTildeFunctor hf).obj M) (toOpensNearVanishing V) (op n))
    (toSectionNearVanishing hf M V t)
  have hinv := ConcreteCategory.congr_hom (IsIso.inv_hom_id (resNearVanishing A (Ideal.span {f}) a
      ((principalTildeFunctor hf).obj M) (toOpensNearVanishing V) (op n)))
    (ConcreteCategory.hom (projNearVanishing A (Ideal.span {f}) a
      ((principalTildeFunctor hf).obj M) (toOpensNearVanishing V) (op n))
      (toSectionNearVanishing hf M V t))
  have hresY : ConcreteCategory.hom (resNearVanishing A (Ideal.span {f}) a
        ((principalTildeFunctor hf).obj M) (toOpensNearVanishing V) (op n))
        (ConcreteCategory.hom (limit.π (formalSections A (Ideal.span {f}) a
          ((principalTildeFunctor hf).obj M)) (op n))
          (ConcreteCategory.hom (comparisonAt A (Ideal.span {f}) a
            ((principalTildeFunctor hf).obj M) (toOpensNearVanishing V))
            (toSectionNearVanishing hf M V t))) =
      ConcreteCategory.hom (projNearVanishing A (Ideal.span {f}) a
        ((principalTildeFunctor hf).obj M) (toOpensNearVanishing V) (op n))
        (toSectionNearVanishing hf M V t) :=
    (congrArg (ConcreteCategory.hom (resNearVanishing A (Ideal.span {f}) a
      ((principalTildeFunctor hf).obj M) (toOpensNearVanishing V) (op n))) hπ).trans hinv
  have hspec := congrArg (fun k => Scheme.Modules.Hom.app k (toOpensNearVanishing V).openSet)
    (cokernel_π_comp_principalTermIso hf M n)
  have hspec' := ConcreteCategory.congr_hom hspec (toSectionNearVanishing hf M V t)
  have hcompsplit := hom_app_comp_apply
    (cokernel.π (C := (complementZeroLocus A a : Scheme).Modules)
      (idealPowerMultiple (idealSheafNearVanishing A (Ideal.span {f}) a) n
        ((principalTildeFunctor hf).obj M)).ι)
    (principalTermIso hf M n).hom (toOpensNearVanishing V).openSet
    (toSectionNearVanishing hf M V t)
  refine (bijective_restrict_quot A a f M V n).1
    (Eq.trans ?_ (restrict_extendQuot A a f M V n
      (moduleSectionsMap (quotMk f M n) V.carrier t)).symm)
  calc moduleSectionsRestrict (Quot f M n) V.le_complement
        (formalLevel hf M n (ConcreteCategory.hom (comparisonAt A (Ideal.span {f}) a
          ((principalTildeFunctor hf).obj M) (toOpensNearVanishing V))
          (toSectionNearVanishing hf M V t)))
      = moduleSectionsCongr (Quot f M n) (image_toOpensNearVanishing V)
          (((principalTildeFunctor hf).obj (Quot f M n)).presheaf.map
            (homOfLE (le_top (a := (toOpensNearVanishing V).openSet))).op
            (Scheme.Modules.Hom.app (principalTermIso hf M n).hom ⊤
              (ConcreteCategory.hom (limit.π (formalSections A (Ideal.span {f}) a
                ((principalTildeFunctor hf).obj M)) (op n))
                (ConcreteCategory.hom (comparisonAt A (Ideal.span {f}) a
                  ((principalTildeFunctor hf).obj M) (toOpensNearVanishing V))
                  (toSectionNearVanishing hf M V t))))) := rfl
    _ = moduleSectionsCongr (Quot f M n) (image_toOpensNearVanishing V)
          (Scheme.Modules.Hom.app (principalTermIso hf M n).hom
            (toOpensNearVanishing V).openSet
            (ConcreteCategory.hom (projNearVanishing A (Ideal.span {f}) a
              ((principalTildeFunctor hf).obj M) (toOpensNearVanishing V) (op n))
              (toSectionNearVanishing hf M V t))) :=
        congrArg (moduleSectionsCongr (Quot f M n) (image_toOpensNearVanishing V))
          ((hom_app_naturality (principalTermIso hf M n).hom
            (le_top (a := (toOpensNearVanishing V).openSet))
            (ConcreteCategory.hom (limit.π (formalSections A (Ideal.span {f}) a
              ((principalTildeFunctor hf).obj M)) (op n))
              (ConcreteCategory.hom (comparisonAt A (Ideal.span {f}) a
                ((principalTildeFunctor hf).obj M) (toOpensNearVanishing V))
                (toSectionNearVanishing hf M V t)))).symm.trans
            (congrArg (Scheme.Modules.Hom.app (principalTermIso hf M n).hom
              (toOpensNearVanishing V).openSet) hresY))
    _ = moduleSectionsCongr (Quot f M n) (image_toOpensNearVanishing V)
          (moduleSectionsMap (quotMk f M n)
            ((complementZeroLocus A a).ι ''ᵁ (toOpensNearVanishing V).openSet)
            (toSectionNearVanishing hf M V t)) :=
        congrArg (moduleSectionsCongr (Quot f M n) (image_toOpensNearVanishing V))
          (hcompsplit.symm.trans (hspec'.trans
            (hom_app_principalTildeFunctor_map hf (quotMk f M n)
              (toOpensNearVanishing V).openSet (toSectionNearVanishing hf M V t))))
    _ = moduleSectionsMap (quotMk f M n) V.carrier t :=
        (moduleSectionsMap_restrict (quotMk f M n)
          (image_toOpensNearVanishing V).ge (toSectionNearVanishing hf M V t)).symm.trans
          (congrArg (moduleSectionsMap (quotMk f M n) V.carrier)
            (moduleSectionsCongr_congr_symm (image_toOpensNearVanishing V) t))

/-! ### Stacks 0EIH for the comparison map of Stacks 0EG2 -/

/-- **[Stacks, Tag 0EIH] in the vocabulary of [Stacks, Tag 0EG2].** Let `A` be Noetherian, let
`f ∈ 𝔞 ⊆ A`, let `M` be a finite `A`-module, and assume `A` is `f`-adically complete, `f` is a
nonzerodivisor on `M`, and `H¹_𝔞(M/fM)` is a finite `A`-module. Then the comparison map of
[Stacks, Tag 0EG2] for the sheaf `M̃|_U` on `U = Spec(A) ∖ V(𝔞)` at the ideal `(f)` is an
isomorphism.

Injectivity is `Stacks.Algebraization.mono_comparisonMap`, which needs nothing beyond coherence.
Surjectivity is the realization of every formal section on a single neighbourhood of the formal
locus (`Stacks.Algebraization.isIso_comparisonMap_iff_realized`), and that is
`Stacks.Algebraization.FormalSections.isIso_formalComparison` read through the translation of
formal sections and of neighbourhoods above. -/
public theorem isIso_comparisonMap_principalTilde (hf : f ∈ a) (M : ModuleCat.{u} A)
    [Module.Finite A (M : Type u)] [IsAdicComplete (Ideal.span {f}) A]
    (hreg : IsSMulRegular (M : Type u) f)
    (hH1 : Module.Finite A
      (localCohomologyModule A a (Ideal.fg_of_isNoetherianRing a) (Quot f M 1) 1)) :
    IsIso (comparisonMap A (Ideal.span {f}) a ((principalTildeFunctor hf).obj M)) := by
  have : ((principalTildeFunctor hf).obj M).IsCoherent := (coherentPrincipalTilde hf M).property
  refine (isIso_comparisonMap_iff_realized A (Ideal.span {f}) a
    ((principalTildeFunctor hf).obj M)).2 fun s => ?_
  obtain ⟨z, hz⟩ := ((ConcreteCategory.isIso_iff_bijective
      (ModuleCat.ofHom (formalComparison A a f M))).1
    (isIso_formalComparison A f a hf M hreg hH1)).2 (toFormalLimitOfSection hf M s)
  obtain ⟨V, t, rfl⟩ := Module.DirectLimit.exists_of z
  refine ⟨toOpensNearVanishing V, toSectionNearVanishing hf M V t,
    toFormalLimitOfSection_injective hf M (Eq.trans ?_ hz)⟩
  refine Eq.trans ?_ (formalComparison_of A a f M V t).symm
  refine Subtype.ext (funext fun n => ?_)
  have hsucc : ∀ k : ℕ, (toFormalLimitOfSection hf M
        (ConcreteCategory.hom (comparisonAt A (Ideal.span {f}) a
          ((principalTildeFunctor hf).obj M) (toOpensNearVanishing V))
          (toSectionNearVanishing hf M V t))).1 (k + 1) =
      (nbhdComparison A a f M V t).1 (k + 1) := fun k =>
    (toFormalLimitOfSection_succ hf M _ k).trans
      ((formalLevel_comparisonAt hf M (k + 1) V t).trans
        (nbhdComparison_apply A a f M V t (k + 1)).symm)
  cases n with
  | succ k => exact hsucc k
  | zero =>
    exact (congrArg (moduleSectionsMap (quotLe f M (Nat.le_succ 0)) (complOpen A a))
      (hsucc 0)).trans ((nbhdComparison A a f M V t).2 0)

end Noetherian

end Stacks.Algebraization

end

end
