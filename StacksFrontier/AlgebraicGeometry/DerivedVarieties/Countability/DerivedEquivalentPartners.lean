module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Countability.DerivedEquivalenceFamilies
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Countability.FibreIsomorphismClasses
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Countability.RelativeEquivalenceKernels
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.KernelBaseChange
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.RelativeEquivalenceBaseChangeDischarged
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.NoDeformations.LocalTriviality
import StacksCore.Tactic.StacksAttribute

/-!
# Derived equivalent partners: base change onto a constant family, and the count

Let `S` be a scheme over a field `K`, let `X` and `Y` be schemes over `S`, let `X₀` be a scheme
over `K` and let `M` be the Fourier–Mukai kernel of a relative equivalence from `X` to `Y` over
`S`. Suppose `T ⟶ S` is a morphism over which `X` becomes the constant family, i.e. there is an
isomorphism `X₀ ×_K T ≅ X ×_S T` over `T`. Then there is a Fourier–Mukai kernel of a relative
equivalence from `X₀ ×_K T` to `Y ×_S T` over `T`.

This is the step of the proof of [Stacks, Tag 0G11] that reads "Denote `M_i` the pullback of `M`.
By Lemma 0G0K `M_i` is the Fourier–Mukai kernel of a relative equivalence from `X_i` to `Y_i`
over `S_i`", followed by the source's silent identification of `X_i` with `𝐗 × S_i` along the
isomorphism `h_i` of [Stacks, Tag 0G0X] — which is what lets [Stacks, Tag 0G0S], whose
hypothesis is a kernel on a *constant* first family, be applied. The identification is not
free: `IsRelativeEquivalenceKernel` is a predicate on a specific pair of morphisms, so moving it
across an isomorphism of the source family is a theorem, namely
`AlgebraicGeometry.isRelativeEquivalenceKernel_derivedPullback_of_iso`.

## Main results

* `AlgebraicGeometry.exists_isRelativeEquivalenceKernel_constantFamily_baseChange` — the kernel
  on the constant family over `T`, from the kernel over `S` and the trivialising isomorphism.
* `AlgebraicGeometry.countable_fibreClassSet_of_isRelativeEquivalenceKernel` — the second
  paragraph of the proof of [Stacks, Tag 0G11].
* `AlgebraicGeometry.countable_isomorphismClasses_of_countable_relativeEquivalenceSystems` — the
  first paragraph: a countable family of relative equivalences accounting for every scheme with
  a property `D` bounds the isomorphism classes of such schemes.
* `AlgebraicGeometry.countable_isomorphismClasses_derivedEquivalent_of_relativeEquivalenceFamilies`
  — [Stacks, Tag 0G11] from the statement of [Stacks, Tag 0G0Y].
* `AlgebraicGeometry.countable_isomorphismClasses_derivedEquivalent` — [Stacks, Tag 0G11].

## Implementation notes

The constant family `X₀ ×_K T` is `(Over.pullback (T.hom ≫ S.hom)).obj X₀`, whose structure
morphism is `pullback.snd X₀.hom (T.hom ≫ S.hom)`, and the base change `X ×_S T` is
`(Over.pullback T.hom).obj X`. The trivialising datum is an isomorphism in `Over T.left` between
`X₀ ×_K S` base changed to `T` and `X` base changed to `T`, which is exactly the shape in which
[Stacks, Tag 0G0X] (`exists_countable_finiteType_isomorphism_families_of_isAlgClosed`) delivers
it.

[Stacks, Tag 0G0K] is used in its unconditional form
`AlgebraicGeometry.isRelativeEquivalenceKernel_baseChange`, [Stacks, Tag 0G0S] as
`AlgebraicGeometry.isLocallyConstantFamily_of_isRelativeEquivalenceKernel` and [Stacks, Tag 0G0Y]
as `AlgebraicGeometry.exists_countable_relativeEquivalenceKernels`.

## References

* [Stacks Project, Tag 0G11](https://stacks.math.columbia.edu/tag/0G11)
* [Stacks Project, Tag 0G0K](https://stacks.math.columbia.edu/tag/0G0K)
* [Stacks Project, Tag 0G0S](https://stacks.math.columbia.edu/tag/0G0S)
* [Stacks Project, Tag 0G0X](https://stacks.math.columbia.edu/tag/0G0X)
* [Stacks Project, Tag 0G0Y](https://stacks.math.columbia.edu/tag/0G0Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

/-- **The base change of a relative equivalence onto a constant source family.** Let `M` be the
Fourier–Mukai kernel of a relative equivalence from `X` to `Y` over `S`, let `X₀` be a scheme
over the base field, and let `T ⟶ S` be a morphism together with an isomorphism
`e : X₀ ×_K S ×_S T ≅ X ×_S T` over `T` trivialising `X` over `T`. Then some object is the
Fourier–Mukai kernel of a relative equivalence from the constant family `X₀ ×_K T` to `Y ×_S T`
over `T`.

Proof: [Stacks, Tag 0G0K] base changes `M` along `T ⟶ S` to a kernel from `X ×_S T` to `Y ×_S T`
over `T`; `e`, composed with the canonical comparison
`X₀ ×_K T ≅ (X₀ ×_K S) ×_S T`, is an isomorphism over `T` from the constant family to `X ×_S T`,
and `isRelativeEquivalenceKernel_derivedPullback_of_iso` carries the kernel across it. -/
theorem exists_isRelativeEquivalenceKernel_constantFamily_baseChange
    {k : Type u} [Field k] (S : Over (Spec (CommRingCat.of k))) (X Y : Over S.left)
    (X₀ : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [IsSeparated Y.hom] [Flat X.hom] [Flat Y.hom]
    [QuasiCompact X.hom] [QuasiSeparated X.hom] [QuasiCompact Y.hom] [QuasiSeparated Y.hom]
    (T : Over S.left)
    (e : (Over.pullback T.hom).obj ((Over.pullback S.hom).obj X₀) ≅
      (Over.pullback T.hom).obj X)
    {M : DerivedCategory (pullback X.hom Y.hom).Modules}
    (hM : IsRelativeEquivalenceKernel X.hom Y.hom M) :
    ∃ N : DerivedCategory (pullback ((Over.pullback (T.hom ≫ S.hom)).obj X₀).hom
      ((Over.pullback T.hom).obj Y).hom).Modules,
      IsRelativeEquivalenceKernel ((Over.pullback (T.hom ≫ S.hom)).obj X₀).hom
        ((Over.pullback T.hom).obj Y).hom N := by
  -- [Stacks, Tag 0G0K]: base change the kernel along `T ⟶ S`
  have hbc := isRelativeEquivalenceKernel_baseChange X.hom Y.hom T.hom hM
  -- the trivialising isomorphism, over `T`, out of the constant family
  let eOver : (Over.pullback (T.hom ≫ S.hom)).obj X₀ ≅ (Over.pullback T.hom).obj X :=
    (Over.pullbackComp T.hom S.hom).app X₀ ≪≫ e
  let eX : ((Over.pullback (T.hom ≫ S.hom)).obj X₀).left ≅ pullback X.hom T.hom :=
    (Over.forget T.left).mapIso eOver
  have hf : eX.hom ≫ pullback.snd X.hom T.hom =
      ((Over.pullback (T.hom ≫ S.hom)).obj X₀).hom := Over.w eOver.hom
  exact ⟨_, isRelativeEquivalenceKernel_derivedPullback_of_iso
    (pullback.snd X.hom T.hom) (pullback.snd Y.hom T.hom) eX (Iso.refl _) hf
    (Category.id_comp _) hbc⟩

section Assembly

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **The inner paragraph of [Stacks, Tag 0G11].** Let `k` be algebraically closed, let `S` be of
finite type over `k`, let `X ⟶ S` and `Y ⟶ S` be smooth proper, let `X₀` be
smooth proper over `k`, and let `M` be the Fourier–Mukai kernel of a relative equivalence from
`X` to `Y` over `S`. Then the fibres `Y_t` at those `k`-points `t` of `S` with `X_t ≅ X₀` fall
into countably many isomorphism classes over `k`.

This is the source's second paragraph in full: [Stacks, Tag 0G0X] produces the countable family
of finite-type `T ⟶ S` trivialising `X`, [Stacks, Tag 0G0K] and
`exists_isRelativeEquivalenceKernel_constantFamily_baseChange` put the kernel on the constant
family over each `T`, [Stacks, Tag 0G0S] makes `Y ×_S T ⟶ T` locally
constant, and `countable_fibreClassSet_of_locallyConstant_baseChanges` assembles the count. -/
theorem countable_fibreClassSet_of_isRelativeEquivalenceKernel
    (S : Over (Spec (CommRingCat.of k))) [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    (X Y : Over S.left)
    [Smooth X.hom] [IsProper X.hom] [Smooth Y.hom] [IsProper Y.hom]
    (X₀ : Over (Spec (CommRingCat.of k)))
    [Smooth X₀.hom] [IsProper X₀.hom]
    {M : DerivedCategory (pullback X.hom Y.hom).Modules}
    (hM : IsRelativeEquivalenceKernel X.hom Y.hom M) :
    (fibreClassSet S.hom Y (fun t => Nonempty (fibreOver X t ≅ X₀))).Countable := by
  refine countable_fibreClassSet_of_locallyConstant_baseChanges S X Y X₀ ?_
  intro T _ _ he
  have : Smooth ((Over.pullback T.hom).obj Y).hom :=
    inferInstanceAs (Smooth (pullback.snd Y.hom T.hom))
  have : IsProper ((Over.pullback T.hom).obj Y).hom :=
    inferInstanceAs (IsProper (pullback.snd Y.hom T.hom))
  obtain ⟨N, hN⟩ := exists_isRelativeEquivalenceKernel_constantFamily_baseChange S X Y X₀ T
    (Classical.choice he) hM
  exact isLocallyConstantFamily_of_isRelativeEquivalenceKernel X₀.hom (T.hom ≫ S.hom)
    ((Over.pullback T.hom).obj Y).hom N hN

/-- **The first paragraph of [Stacks, Tag 0G11].** Let `D` be a
condition on schemes over an algebraically closed field `k` — the intended reading is "smooth,
proper and derived equivalent to `X₀`". Suppose a countable family of systems
`(S i, X i ⟶ S i, Y i ⟶ S i, M i)` with `S i` of finite type over `k`, `X i` and `Y i` smooth
proper over `S i` and `M i` the Fourier–Mukai kernel of a relative equivalence from `X i` to
`Y i` over `S i` accounts for every `Z` satisfying `D`, in the sense of property (4) of
[Stacks, Tag 0G0Y]. Then the schemes satisfying `D` fall into countably many isomorphism classes
over `k`.

Together with [Stacks, Tag 0G0Y] — which produces exactly such a countable family, with
property (4) for `D Z` = "`Z` is smooth and proper and there is a `k`-linear exact equivalence
`D_perf(𝒪_{X₀}) ⟶ D_perf(𝒪_Z)`" — this is [Stacks, Tag 0G11]; see
`countable_isomorphismClasses_derivedEquivalent_of_relativeEquivalenceFamilies`. -/
theorem countable_isomorphismClasses_of_countable_relativeEquivalenceSystems
    {D : Over (Spec (CommRingCat.of k)) → Prop} (X₀ : Over (Spec (CommRingCat.of k)))
    [Smooth X₀.hom] [IsProper X₀.hom]
    {I : Type*} [Countable I] (S : I → Over (Spec (CommRingCat.of k)))
    (hS : ∀ i, LocallyOfFiniteType (S i).hom ∧ QuasiCompact (S i).hom)
    (X Y : ∀ i, Over (S i).left)
    (hX : ∀ i, Smooth (X i).hom ∧ IsProper (X i).hom)
    (hY : ∀ i, Smooth (Y i).hom ∧ IsProper (Y i).hom)
    (M : ∀ i, DerivedCategory (pullback (X i).hom (Y i).hom).Modules)
    (hM : ∀ i, IsRelativeEquivalenceKernel (X i).hom (Y i).hom (M i))
    (haccount : ∀ Z : Over (Spec (CommRingCat.of k)), D Z →
      ∃ i, ∃ t : Spec (CommRingCat.of k) ⟶ (S i).left, t ≫ (S i).hom = 𝟙 _ ∧
        Nonempty (fibreOver (X i) t ≅ X₀) ∧ Nonempty (fibreOver (Y i) t ≅ Z)) :
    {c : IsomorphismClassOver k | ∃ Z, D Z ∧ c = isomorphismClassOver Z}.Countable := by
  refine countable_isomorphismClasses_of_countable_systems X₀ S X Y haccount fun i => ?_
  obtain ⟨_, _⟩ := hS i
  obtain ⟨_, _⟩ := hX i
  obtain ⟨_, _⟩ := hY i
  exact countable_fibreClassSet_of_isRelativeEquivalenceKernel (S i) (X i) (Y i) X₀ (hM i)

/-- **[Stacks, Tag 0G11] from the statement of [Stacks, Tag 0G0Y].** Let `K` be an algebraically
closed field and `X₀` a smooth proper scheme over `K`. Given the countable family of
[Stacks, Tag 0G0Y] (the hypothesis `h0G0Y`, verbatim the conclusion of
`exists_countable_relativeEquivalenceKernels`), the smooth
proper schemes `Y` over `K` admitting a `K`-linear exact equivalence
`D_perf(𝒪_{X₀}) ⟶ D_perf(𝒪_Y)` fall into at most countably many isomorphism classes over `K`.

Proof: property (4) of [Stacks, Tag 0G0Y] applied to `(X₀, Y)` is the accounting hypothesis of
`countable_isomorphismClasses_of_countable_relativeEquivalenceSystems`, at the `K`-point
`s.left` of `S i`. -/
theorem countable_isomorphismClasses_derivedEquivalent_of_relativeEquivalenceFamilies
    (h0G0Y : ∃ (I : Type (u + 1)) (_ : Countable I)
      (S : I → Over (Spec (.of k)))
      (X Y : (i : I) → Over (S i).left)
      (M : (i : I) → DerivedCategory (pullback (X i).hom (Y i).hom).Modules)
      (_ : ∀ i, LocallyOfFiniteType (S i).hom ∧ QuasiCompact (S i).hom)
      (_ : ∀ i, Smooth (X i).hom ∧ IsProper (X i).hom)
      (_ : ∀ i, Smooth (Y i).hom ∧ IsProper (Y i).hom)
      (_ : ∀ i, IsRelativeEquivalenceKernel (X i).hom (Y i).hom (M i)),
      ∀ (A B : Over (Spec (.of k))),
        Smooth A.hom → IsProper A.hom → Smooth B.hom → IsProper B.hom →
          (letI : Linear k A.left.Modules := modulesLinear k A
           letI : Linear k B.left.Modules := modulesLinear k B
           ∃ e : Stacks.Perfect.BoundedLocallyFreeComplexes.PerfectDerivedCategory A.left ≌
               Stacks.Perfect.BoundedLocallyFreeComplexes.PerfectDerivedCategory B.left,
             e.functor.Linear k ∧
               ∃ h : e.functor.CommShift ℤ,
                 letI := h
                 e.functor.IsTriangulated) →
            ∃ (i : I) (s : Over.mk (𝟙 (Spec (.of k))) ⟶ S i),
              Nonempty (A ≅ (Over.pullback s.left).obj (X i)) ∧
                Nonempty (B ≅ (Over.pullback s.left).obj (Y i)))
    (X₀ : Over (Spec (CommRingCat.of k))) [Smooth X₀.hom] [IsProper X₀.hom] :
    {c : IsomorphismClassOver k | ∃ Y : Over (Spec (CommRingCat.of k)),
      Smooth Y.hom ∧ IsProper Y.hom ∧
        (letI : Linear k X₀.left.Modules := modulesLinear k X₀
         letI : Linear k Y.left.Modules := modulesLinear k Y
         ∃ e : Stacks.Perfect.BoundedLocallyFreeComplexes.PerfectDerivedCategory X₀.left ≌
             Stacks.Perfect.BoundedLocallyFreeComplexes.PerfectDerivedCategory Y.left,
           e.functor.Linear k ∧
             ∃ h : e.functor.CommShift ℤ,
               letI := h
               e.functor.IsTriangulated) ∧
        c = isomorphismClassOver Y}.Countable := by
  obtain ⟨I, hI, S, X, Y, M, hS, hX, hY, hM, hacc⟩ := h0G0Y
  have hc := countable_isomorphismClasses_of_countable_relativeEquivalenceSystems
    (D := fun Z => Smooth Z.hom ∧ IsProper Z.hom ∧
        (let : Linear k X₀.left.Modules := modulesLinear k X₀
         let : Linear k Z.left.Modules := modulesLinear k Z
         ∃ e : Stacks.Perfect.BoundedLocallyFreeComplexes.PerfectDerivedCategory X₀.left ≌
             Stacks.Perfect.BoundedLocallyFreeComplexes.PerfectDerivedCategory Z.left,
           e.functor.Linear k ∧
             ∃ h : e.functor.CommShift ℤ,
               let := h
               e.functor.IsTriangulated))
    X₀ S hS X Y hX hY M hM fun Z ⟨hZs, hZp, hZe⟩ => by
      obtain ⟨i, s, ⟨eX⟩, ⟨eY⟩⟩ := hacc X₀ Z inferInstance inferInstance hZs hZp hZe
      exact ⟨i, s.left, by simp, ⟨eX.symm⟩, ⟨eY.symm⟩⟩
  refine hc.mono ?_
  rintro c ⟨Z, hZs, hZp, hZe, rfl⟩
  exact ⟨Z, ⟨hZs, hZp, hZe⟩, rfl⟩

/-- **Stacks Project, Tag 0G11.** Let `K` be an algebraically closed field and let `X₀` be a
smooth proper scheme over `K`. There are at most countably many isomorphism classes of smooth
proper schemes `Y` over `K` which are derived equivalent to `X₀`, i.e. admit a `K`-linear exact
equivalence `D_perf(𝒪_{X₀}) ⟶ D_perf(𝒪_Y)` ([Stacks, Tag 0G10]).

Proof: [Stacks, Tag 0G0Y] (`exists_countable_relativeEquivalenceKernels`) produces the countable
family of relative equivalences, and
`countable_isomorphismClasses_derivedEquivalent_of_relativeEquivalenceFamilies` counts. -/
@[stacks 0G11]
theorem countable_isomorphismClasses_derivedEquivalent
    (X₀ : Over (Spec (CommRingCat.of k))) [Smooth X₀.hom] [IsProper X₀.hom] :
    {c : IsomorphismClassOver k | ∃ Y : Over (Spec (CommRingCat.of k)),
      Smooth Y.hom ∧ IsProper Y.hom ∧
        (letI : Linear k X₀.left.Modules := modulesLinear k X₀
         letI : Linear k Y.left.Modules := modulesLinear k Y
         ∃ e : Stacks.Perfect.BoundedLocallyFreeComplexes.PerfectDerivedCategory X₀.left ≌
             Stacks.Perfect.BoundedLocallyFreeComplexes.PerfectDerivedCategory Y.left,
           e.functor.Linear k ∧
             ∃ h : e.functor.CommShift ℤ,
               letI := h
               e.functor.IsTriangulated) ∧
        c = isomorphismClassOver Y}.Countable :=
  countable_isomorphismClasses_derivedEquivalent_of_relativeEquivalenceFamilies
    (exists_countable_relativeEquivalenceKernels k) X₀

end Assembly

end AlgebraicGeometry

end
