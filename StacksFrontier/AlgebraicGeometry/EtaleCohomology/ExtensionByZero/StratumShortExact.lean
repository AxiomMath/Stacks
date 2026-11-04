module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleOpens
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero

/-!
# Adding a stratum to an open, extended by zero

Let `W` be a scheme, `V` an open of `W`, `n : N → W` an open immersion and `i : T → N` a closed
immersion whose image in `W` is `n(N) \ V`. Then `T` is closed in the open `V' = V ∪ n(N)`, with
complement `V`, and for a sheaf `L` of `Λ`-modules on `W` there is a short exact sequence

`0 → j_{V!} L|_V → j_{V'!} L|_{V'} → n_! i_* G → 0`,

where `G` is the inverse image of `L` on `T`: this is Tag 095L on `V'` for the closed immersion
`T → V'`, extended by zero to `W`, with `j_{V'!} (T → V')_* = n_! i_*` (`T` is closed in `N`).
It is the step from `V` to `V'` in the proof of Poincaré duality by noetherian induction on the
open where it holds (`Stacks.EtaleCohomology.isDualityPerfect_of_dense_open`).

## Main results

* `Stacks.EtaleCohomology.exists_shortExact_extensionByZero_sup_stratum`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ]

/-- Extension by zero of the identity is the identity, through the counit:
`𝟙_! 𝟙^{-1} F ⟶ F` is an isomorphism. -/
theorem isIso_etaleModuleExtensionByZeroAdj_counit_app_id {T : Scheme.{u}}
    (F : EtaleModules.{u, r} Λ T) :
    IsIso ((etaleModuleExtensionByZeroAdj.{u, r} Λ (𝟙 T)).counit.app F) :=
  isIso_of_isIso_etaleModuleInverseImage_family Λ (T := fun _ : PUnit.{u + 1} => T)
    (fun _ => 𝟙 T) (Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨PUnit.unit, x, rfl⟩) _
    fun _ => isIso_etaleModuleInverseImage_map_counit_of_factors Λ (𝟙 T) (𝟙 T) (𝟙 T)
      (Category.comp_id _) F

variable {W N T : Scheme.{u}} (V : W.Opens) (n : N ⟶ W) [IsOpenImmersion n] (i : T ⟶ N)
  [IsClosedImmersion i]

/-- `j_{a!} L|_a ≅ j_{b!} L|_b` for equal étale morphisms `a = b`. -/
private lemma nonempty_iso_of_eq {U : Scheme.{u}} (a b : U ⟶ W) [Etale a] [Etale b] (h : a = b)
    (L : EtaleModules.{u, r} Λ W) :
    Nonempty ((etaleModuleExtensionByZeroOfRestriction.{u, r} Λ a).obj L ≅
      (etaleModuleExtensionByZeroOfRestriction.{u, r} Λ b).obj L) := by
  subst h
  exact ⟨Iso.refl _⟩

/-- `a_! X ≅ b_! X` for equal étale morphisms `a = b`. -/
private lemma nonempty_iso_extensionByZero_of_eq {U : Scheme.{u}} (a b : U ⟶ W) [Etale a]
    [Etale b] (h : a = b) (X : EtaleModules.{u, r} Λ U) :
    Nonempty ((etaleModuleExtensionByZero.{u, r} Λ a).obj X ≅
      (etaleModuleExtensionByZero.{u, r} Λ b).obj X) := by
  subst h
  exact ⟨Iso.refl _⟩

/-- `x` is in the range of `h` iff `f x` is in the range of `h ≫ f`, for `f` injective. -/
private lemma mem_range_iff_of_injective {X Y Z : Scheme.{u}} (h : X ⟶ Y) (f : Y ⟶ Z)
    (hf : Function.Injective f.base) (y : Y) :
    y ∈ Set.range h.base ↔ f.base y ∈ Set.range (h ≫ f).base :=
  ⟨fun ⟨x, hx⟩ => ⟨x, by simp [← hx]⟩, fun ⟨x, hx⟩ => ⟨x, hf (by simpa using hx)⟩⟩

/-- The range of the inclusion `A ⟶ B` of opens of `W` is the preimage of `A` in `B`. -/
private lemma range_homOfLE_base {A B : W.Opens} (h : A ≤ B) :
    Set.range (W.homOfLE h).base = B.ι.base ⁻¹' (A : Set W) := by
  ext y
  rw [mem_range_iff_of_injective (W.homOfLE h) B.ι B.ι.isOpenEmbedding.injective,
    W.homOfLE_ι, Scheme.Opens.range_ι, Set.mem_preimage]

omit [IsClosedImmersion i] in
/-- For an open `V'` of `W` equal to `V ⊔ n(N)` and a morphism `ι` to `V'` over `i ≫ n`, the
range of `ι` is the complement of `V` in `V'`. -/
private lemma range_eq_preimage_compl_of_comp_eq (V' : W.Opens) (hV' : V' = V ⊔ n.opensRange)
    (hi : Set.range (i ≫ n).base = Set.range n.base \ (V : Set W))
    (ι : T ⟶ V'.toScheme) (hι : ι ≫ V'.ι = i ≫ n) :
    Set.range ι.base = V'.ι.base ⁻¹' (V : Set W)ᶜ := by
  subst hV'
  ext y
  rw [mem_range_iff_of_injective ι _ (Scheme.Opens.ι _).isOpenEmbedding.injective, hι, hi]
  simp only [Set.mem_sdiff, Set.mem_preimage, Set.mem_compl_iff]
  exact ⟨And.right, fun h => ⟨Or.resolve_left y.2 h, h⟩⟩

/-- **Adding a stratum to an open, extended by zero.** For an open `V` of `W`, an open immersion
`n : N → W` and a closed immersion `i : T → N` with image `n(N) \ V` in `W`, there is a short
exact sequence `0 → j_{V!} L|_V → j_{V'!} L|_{V'} → n_! i_* G → 0` (up to isomorphism of its
terms) for `V' = V ∪ n(N)` and a sheaf `G` on `T`, the inverse image of `L` (restricted along the
identity). -/
theorem exists_shortExact_extensionByZero_sup_stratum
    (hi : Set.range (i ≫ n).base = Set.range n.base \ (V : Set W)) (L : EtaleModules.{u, r} Λ W) :
    ∃ S : ShortComplex (EtaleModules.{u, r} Λ W), S.ShortExact ∧
      Nonempty (S.X₁ ≅ (etaleModuleExtensionByZeroOfRestriction.{u, r} Λ V.ι).obj L) ∧
      Nonempty (S.X₂ ≅
        (etaleModuleExtensionByZeroOfRestriction.{u, r} Λ (V ⊔ n.opensRange).ι).obj L) ∧
      Nonempty (S.X₃ ≅ (etaleModuleExtensionByZero.{u, r} Λ n).obj
        ((etaleModuleDirectImage.{u, r} Λ i).obj ((etaleModuleRestriction.{u, r} Λ (𝟙 T)).obj
          ((etaleModuleInverseImage.{u, r} Λ (i ≫ n)).obj L)))) := by
  set V' : W.Opens := V ⊔ n.opensRange with hV'
  let n' : N ⟶ V'.toScheme := IsOpenImmersion.lift V'.ι n (by simp [V'])
  have hn' : n' ≫ V'.ι = n := IsOpenImmersion.lift_fac _ _ _
  let w : V.toScheme ⟶ V'.toScheme := W.homOfLE le_sup_left
  let ι : T ⟶ V'.toScheme := i ≫ n'
  have hιn : ι ≫ V'.ι = i ≫ n := by simp [ι, hn']
  have hrange : Set.range ι.base = V'.ι.base ⁻¹' (V : Set W)ᶜ :=
    range_eq_preimage_compl_of_comp_eq V n i V' hV' hi ι hιn
  have : IsClosedImmersion ι := .of_isPreimmersion _ (by
    rw [hrange]
    exact V.isOpen.isClosed_compl.preimage V'.ι.continuous)
  have hij : Set.range w.base = (Set.range ι.base)ᶜ := by
    rw [hrange, Set.preimage_compl, compl_compl]
    exact range_homOfLE_base le_sup_left
  let M := (etaleModuleRestriction.{u, r} Λ V'.ι).obj L
  obtain ⟨_, hS⟩ := shortExact_etaleModuleExtensionByZero_directImage Λ ι w hij M
  refine ⟨_, hS.map_of_exact (etaleModuleExtensionByZero.{u, r} Λ V'.ι), ?_, ⟨Iso.refl _⟩, ?_⟩
  · obtain ⟨e⟩ := nonempty_iso_of_eq Λ (w ≫ V'.ι) V.ι (W.homOfLE_ι _) L
    exact ⟨((etaleModuleExtensionByZeroCompIso.{u, r} Λ w V'.ι).app _).symm ≪≫
      (etaleModuleExtensionByZero.{u, r} Λ (w ≫ V'.ι)).mapIso
        ((etaleModuleRestrictionCompIso.{u, r} Λ w V'.ι).app L) ≪≫ e⟩
  · let G := (etaleModuleInverseImage.{u, r} Λ ι).obj M
    have sq : IsPullback i (𝟙 T) n' ι := IsPullback.of_vert_isIso_mono ⟨by simp [ι]⟩
    have := isIso_etaleModuleExtensionByZeroAdj_counit_app_id Λ G
    have eG : (etaleModuleInverseImage.{u, r} Λ ι).obj M ≅
        (etaleModuleInverseImage.{u, r} Λ (i ≫ n)).obj L :=
      (etaleModuleInverseImage.{u, r} Λ ι).mapIso
          ((etaleModuleInverseImageRestrictionIso.{u, r} Λ V'.ι).app L).symm ≪≫
        ((etaleModuleInverseImageCompIso.{u, r} Λ ι V'.ι).app L).symm ≪≫
        eqToIso (by rw [hιn])
    obtain ⟨e'⟩ := nonempty_iso_extensionByZero_of_eq Λ (n' ≫ V'.ι) n hn'
      ((etaleModuleDirectImage.{u, r} Λ i).obj ((etaleModuleRestriction.{u, r} Λ (𝟙 T)).obj G))
    exact ⟨(etaleModuleExtensionByZero.{u, r} Λ V'.ι).mapIso
        ((etaleModuleDirectImage.{u, r} Λ ι).mapIso
          (asIso ((etaleModuleExtensionByZeroAdj.{u, r} Λ (𝟙 T)).counit.app G)).symm ≪≫
        ((etaleModuleExtensionByZeroDirectImageIso.{u, r} Λ i (𝟙 T) n' ι sq).app _).symm) ≪≫
      ((etaleModuleExtensionByZeroCompIso.{u, r} Λ n' V'.ι).app _).symm ≪≫
      e' ≪≫
      (etaleModuleExtensionByZero.{u, r} Λ n).mapIso
        ((etaleModuleDirectImage.{u, r} Λ i).mapIso
          ((etaleModuleRestriction.{u, r} Λ (𝟙 T)).mapIso eG))⟩

end Stacks.EtaleCohomology
