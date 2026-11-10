module

public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ProjectiveLineIntegral
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedSite
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekCompactSupportOpen
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSite

/-!
# Compactly supported sections do not form a cosheaf

Let `X` be a separated scheme locally of finite type over a field `k` and let `F` be an abelian
sheaf on the small étale site of `X`. Tag 0F74 says that the injections
`H^0_c(X', F|_{X'}) → H^0_c(X, F)` of extension by zero along open subschemes `X' ⊆ X` turn
`H^0_c` into a "cosheaf" on the Zariski site of `X`; the quotation marks are the source's. Read
literally the cosheaf condition is false: for a Zariski covering `X = U₁ ∪ U₂` the sum map
`H^0_c(U₁) ⊕ H^0_c(U₂) → H^0_c(X)` need not be surjective. This file proves that.

The counterexample is the additive group `𝔾_a`, the sheaf `V ↦ Γ(V, 𝒪_V)` of the small étale site,
on an integral scheme `X` proper over `k`, with any two open subschemes `U₁, U₂ ≠ X`. The global
function `1` is compactly supported, because `X` is proper. A compactly supported section on `Uᵢ`
extends by zero to a global function supported inside `Uᵢ`, so vanishing on the nonempty open
`X \ Uᵢ`; on an integral scheme such a function is zero. Hence the sum map is zero, while
`H^0_c(X, 𝔾_a)` is nonzero. Such data exist over every field: the projective line `ℙ¹_k` is
integral and proper, and the complements of its zero and infinity sections are two proper open
subschemes covering it.

What does hold is recorded in
`StacksFrontier.AlgebraicGeometry.Etale.FShriekCompactSupportOpen`: the maps are injective, they are
the identity for `X' = X` and compose for nested opens, so that `H^0_c` is a precosheaf on the
Zariski site with injective transition maps; the image of `H^0_c(X')` is the group of compactly
supported sections supported inside `X'`; and for two opens the sequence
`0 → H^0_c(U₁ ∩ U₂) → H^0_c(U₁) ⊕ H^0_c(U₂) → H^0_c(U₁ ∪ U₂)` is exact, which is the left end of
the Mayer–Vietoris sequence of compactly supported cohomology whose next term `H^1_c(U₁ ∩ U₂)`
measures the failure of surjectivity.

## Main definitions

* `AlgebraicGeometry.SmallEtale.additiveStructureSheaf` — the additive group `𝔾_a` of the small
  étale site, the structure sheaf with its ring structure forgotten to the additive group.

## Main results

* `AlgebraicGeometry.SmallEtale.eq_zero_of_mem_zeroOpen_additiveStructureSheaf` — on an integral
  scheme a global function vanishing on some nonempty Zariski open is zero.
* `AlgebraicGeometry.SmallEtale.not_surjective_compactlySupportedSections_openInclusion_coprod` —
  on an integral scheme proper over `k`, the sum map from `H^0_c` of two open subschemes
  different from `X` to `H^0_c(X, 𝔾_a)` is not surjective.
* `AlgebraicGeometry.SmallEtale.exists_zariskiCovering_not_surjective_compactlySupportedSections`
  — for every field `k` and every big étale site containing `ℙ¹_k`, there is a Zariski covering
  of `ℙ¹_k` by two open subschemes and an abelian sheaf on which the sum map is not surjective.

## Implementation notes

The support of a section of `𝔾_a` is computed from the definition of the zero open as the union
of the Zariski opens, presented by open immersions of the small étale site, on which the section
restricts to zero. A point of such an open is the image of a point `y` of the source of the open
immersion `φ`, and the germ of `φ^* a` at `y` is the image of the germ of `a` at `φ(y)` under the
stalk map of `φ`, an isomorphism; injectivity of germs on an integral scheme then gives `a = 0`.

## References

* [Stacks Project, Tag 0F74](https://stacks.math.columbia.edu/tag/0F74)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.SmallEtale

section AdditiveGroup

variable (B : BigEtaleSite.{u})

/-- The additive group `𝔾_a` on the small étale site of `S`: the sheaf `V ↦ Γ(V, 𝒪_V)` of
global functions, as a sheaf of abelian groups. -/
public abbrev additiveStructureSheaf (S : Scheme.{u}) (hS : B.Contains S) :
    Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u} :=
  (sheafCompose (SmallEtale.topology B S hS)
    (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u})).obj
    (SmallEtale.commRingStructureSheaf B S hS)

/-- On an integral scheme, a global function lying in the zero open of `𝔾_a` at some point is
zero: it vanishes on a nonempty Zariski open, and germs on an integral scheme are injective. -/
public theorem eq_zero_of_mem_zeroOpen_additiveStructureSheaf (S : Scheme.{u})
    (hS : B.Contains S) [IsIntegral S]
    (a : (additiveStructureSheaf B S hS).obj.obj (op (SmallEtale.final B S hS)))
    {x : (SmallEtale.toScheme B S hS).obj (SmallEtale.final B S hS)}
    (hx : x ∈ zeroOpen B S hS (additiveStructureSheaf B S hS) (SmallEtale.final B S hS) a) :
    a = 0 := by
  obtain ⟨W, hW, hxW⟩ := Opens.mem_sSup.mp hx
  obtain ⟨V, g, hg, hrange, hzero⟩ := hW
  obtain ⟨y, rfl⟩ : x ∈ Set.range ((SmallEtale.toScheme B S hS).map g).base := by
    rwa [← hrange]
  let φ := (SmallEtale.toScheme B S hS).map g
  have : IsIntegral ((SmallEtale.toScheme B S hS).obj (SmallEtale.final B S hS)) :=
    inferInstanceAs (IsIntegral S)
  let T := (SmallEtale.toScheme B S hS).obj (SmallEtale.final B S hS)
  let a' : Γ(T, ⊤) := a
  have hmem : φ.base y ∈ (⊤ : T.Opens) := Set.mem_univ _
  have key : φ.stalkMap y (T.presheaf.germ ⊤ (φ.base y) hmem a') = 0 := by
    refine (Scheme.Hom.germ_stalkMap_apply φ ⊤ y hmem a').trans ?_
    change ((SmallEtale.toScheme B S hS).obj V).presheaf.germ _ y _ (φ.appTop a') = 0
    rw [show φ.appTop a' = 0 from hzero, map_zero]
  change a' = 0
  apply germ_injective_of_isIntegral T (φ.base y) hmem
  apply (ConcreteCategory.bijective_of_isIso (φ.stalkMap y)).1
  rw [key, map_zero, map_zero]

/-- On an integral scheme, a global function of `𝔾_a` whose support misses some point is zero. -/
public theorem eq_zero_of_supportSection_ne_univ_additiveStructureSheaf (S : Scheme.{u})
    (hS : B.Contains S) [IsIntegral S]
    (a : (additiveStructureSheaf B S hS).obj.obj (op (SmallEtale.final B S hS)))
    (ha : supportSection B S hS (additiveStructureSheaf B S hS) (SmallEtale.final B S hS) a ≠
      Set.univ) :
    a = 0 := by
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem _).mp ha
  exact eq_zero_of_mem_zeroOpen_additiveStructureSheaf B S hS a (not_not.mp hx)

end AdditiveGroup

section NotCosheaf

variable (k : Type u) [Field k] (B : BigEtaleSite.{u})

/-- **Stacks 0F74, the cosheaf condition fails.** Let `X` be an integral scheme proper over a
field `k` and let `U₁, U₂ ⊆ X` be open subschemes different from `X`. Then the sum of the two
extension-by-zero maps `H^0_c(U₁, 𝔾_a) ⊕ H^0_c(U₂, 𝔾_a) → H^0_c(X, 𝔾_a)` is not surjective: it is
zero, because a compactly supported section on `Uᵢ` extends to a global function vanishing on the
nonempty open `X \ Uᵢ`, while the function `1` is compactly supported and nonzero. -/
public theorem not_surjective_compactlySupportedSections_openInclusion_coprod
    {X₁ X₂ X : B.Scheme} (j₁ : X₁ ⟶ X) (j₂ : X₂ ⟶ X) (f : X.obj ⟶ Spec (.of k))
    [IsProper f] [IsIntegral X.obj]
    [IsOpenImmersion (B.inclusion.map j₁)] [IsOpenImmersion (B.inclusion.map j₂)]
    (h₁ : Set.range (B.inclusion.map j₁).base ≠ Set.univ)
    (h₂ : Set.range (B.inclusion.map j₂).base ≠ Set.univ) :
    ¬ Function.Surjective
      ((compactlySupportedSections_openInclusion k B j₁ f
          (additiveStructureSheaf B X.obj X.property)).1.coprod
        (compactlySupportedSections_openInclusion k B j₂ f
          (additiveStructureSheaf B X.obj X.property)).1) := by
  let G := additiveStructureSheaf B X.obj X.property
  let T := (SmallEtale.toScheme B X.obj X.property).obj (SmallEtale.final B X.obj X.property)
  have : IsIntegral T := inferInstanceAs (IsIntegral X.obj)
  let one : G.obj.obj (op (SmallEtale.final B X.obj X.property)) := (1 : Γ(T, ⊤))
  have hone : one ∈ compactlySupportedSections k X.obj f B X.property G := by
    rw [mem_compactlySupportedSections]
    change IsProper ((Scheme.IdealSheafData.vanishingIdeal _).subschemeι ≫ f)
    infer_instance
  have hzero (Y : B.Scheme) (j : Y ⟶ X) [IsOpenImmersion (B.inclusion.map j)]
      (hj : Set.range (B.inclusion.map j).base ≠ Set.univ) (s) :
      ((compactlySupportedSections_openInclusion k B j f G).1 s).1 = 0 := by
    apply eq_zero_of_supportSection_ne_univ_additiveStructureSheaf B X.obj X.property
    rw [((compactlySupportedSections_openInclusion k B j f G).property.2 s).2]
    intro h
    exact hj (Set.eq_univ_of_univ_subset (h.symm.subset.trans (Set.image_subset_range _ _)))
  intro hsurj
  obtain ⟨⟨s₁, s₂⟩, hs⟩ := hsurj ⟨one, hone⟩
  have h := congrArg Subtype.val hs
  rw [AddMonoidHom.coprod_apply, AddSubgroup.coe_add, hzero X₁ j₁ h₁ s₁, hzero X₂ j₂ h₂ s₂,
    add_zero] at h
  exact one_ne_zero (α := Γ(T, ⊤)) h.symm

/-- **Stacks 0F74, the cosheaf condition fails for an actual Zariski covering.** For every field
`k` and every big étale site containing the projective line `ℙ¹_k`, the scheme `ℙ¹_k`, separated
and of finite type (indeed proper) over `k`, has a Zariski covering by two open subschemes — the
complements of the zero and of the infinity section — and an abelian sheaf on its small étale
site — the additive group `𝔾_a` — such that the sum of the extension-by-zero maps
`H^0_c(U₁) ⊕ H^0_c(U₂) → H^0_c(ℙ¹_k)` is not surjective. So `H^0_c` is not a cosheaf on the
Zariski site in the literal sense; it is a precosheaf with injective transition maps, see
`AlgebraicGeometry.SmallEtale.compactlySupportedSections_openInclusion`. -/
@[stacks 0F74 "the cosheaf condition is false in the literal sense: a Zariski covering of \
ℙ¹_k by two opens on which the sum map H^0_c(U₁) ⊕ H^0_c(U₂) → H^0_c(ℙ¹_k, 𝔾_a) is not \
surjective"]
public theorem exists_zariskiCovering_not_surjective_compactlySupportedSections
    (hP : B.Contains (Stacks.Chow.relativeProjectiveLine (Spec (.of k)))) :
    ∃ (X X₁ X₂ : B.Scheme) (j₁ : X₁ ⟶ X) (j₂ : X₂ ⟶ X) (f : X.obj ⟶ Spec (.of k))
      (_ : IsProper f) (_ : IsOpenImmersion (B.inclusion.map j₁))
      (_ : IsOpenImmersion (B.inclusion.map j₂)),
      Set.range (B.inclusion.map j₁).base ∪ Set.range (B.inclusion.map j₂).base = Set.univ ∧
      ∃ F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u},
        ¬ Function.Surjective
          ((compactlySupportedSections_openInclusion k B j₁ f F).1.coprod
            (compactlySupportedSections_openInclusion k B j₂ f F).1) := by
  let S : Scheme.{u} := Spec (.of k)
  let P := Stacks.Chow.relativeProjectiveLine S
  let R₀ : Set P := Set.range (Stacks.Chow.lineZeroSection S)
  let R₁ : Set P := Set.range (Stacks.Chow.lineInfinitySection S)
  have hR₀ : IsClosed R₀ := (Stacks.Chow.lineZeroSection S).isClosedEmbedding.isClosed_range
  have hR₁ : IsClosed R₁ := (Stacks.Chow.lineInfinitySection S).isClosedEmbedding.isClosed_range
  let U₀ : P.Opens := ⟨R₀ᶜ, hR₀.isOpen_compl⟩
  let U₁ : P.Opens := ⟨R₁ᶜ, hR₁.isOpen_compl⟩
  let X : B.Scheme := B.obj P hP
  let X₀ : B.Scheme := B.obj U₀ (BigEtaleOver.contains_opens B hP U₀)
  let X₁ : B.Scheme := B.obj U₁ (BigEtaleOver.contains_opens B hP U₁)
  let j₀ : X₀ ⟶ X := ObjectProperty.homMk U₀.ι
  let j₁ : X₁ ⟶ X := ObjectProperty.homMk U₁.ι
  have hj₀ : B.inclusion.map j₀ = U₀.ι := rfl
  have hj₁ : B.inclusion.map j₁ = U₁.ι := rfl
  have : IsOpenImmersion (B.inclusion.map j₀) := inferInstanceAs (IsOpenImmersion U₀.ι)
  have : IsOpenImmersion (B.inclusion.map j₁) := inferInstanceAs (IsOpenImmersion U₁.ι)
  let f : X.obj ⟶ Spec (.of k) := P ↘ S
  have : IsProper f := Stacks.Chow.isProper_relativeProjectiveLine_over S
  have : IsIntegral X.obj := inferInstanceAs (IsIntegral P)
  have hr₀ : Set.range (B.inclusion.map j₀).base = R₀ᶜ := by
    rw [hj₀, Scheme.Opens.range_ι]
    rfl
  have hr₁ : Set.range (B.inclusion.map j₁).base = R₁ᶜ := by
    rw [hj₁, Scheme.Opens.range_ι]
    rfl
  obtain ⟨s⟩ : Nonempty S := inferInstance
  refine ⟨X, X₀, X₁, j₀, j₁, f, inferInstance, inferInstance, inferInstance, ?_,
    additiveStructureSheaf B X.obj X.property, ?_⟩
  · rw [hr₀, hr₁, ← Set.compl_inter,
      (Stacks.Chow.disjoint_range_lineZeroSection_lineInfinitySection S).inter_eq,
      Set.compl_empty]
  · refine not_surjective_compactlySupportedSections_openInclusion_coprod k B j₀ j₁ f ?_ ?_
    · rw [hr₀]
      intro h
      have hm : (Stacks.Chow.lineZeroSection S) s ∈ R₀ᶜ := h ▸ Set.mem_univ _
      exact hm ⟨s, rfl⟩
    · rw [hr₁]
      intro h
      have hm : (Stacks.Chow.lineInfinitySection S) s ∈ R₁ᶜ := h ▸ Set.mem_univ _
      exact hm ⟨s, rfl⟩

end NotCosheaf

end AlgebraicGeometry.SmallEtale

end
