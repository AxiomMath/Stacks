module

public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionSequence
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeData

/-!
# The two assertions of Tag 0C6K are equivalent

Let `L` be an invertible module on a scheme `X`, let `s` be a global section and write
`f : 𝒪_X ⟶ L` for multiplication by `s`. Let `i : Z(s) ⟶ X` be the inclusion of the zero scheme
of `s` and `g : L ⟶ i_* i^* L` the unit of the pullback–pushforward adjunction.
[Stacks, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K) asserts two things:

1. `g` realizes `i_* i^* L` as the cokernel of `f`, i.e. there is an isomorphism
   `e : coker f ≅ i_* i^* L` with `coker.π f ≫ e.hom = g`;
2. for a regular section, `0 ⟶ 𝒪_X ⟶ L ⟶ i_* i^* L ⟶ 0` is short exact.

`AlgebraicGeometry.Scheme.Modules.shortExact_of_isRegularSection_of_cokernelIso` derives (2) from
(1). This file proves the converse, so that for a regular section the two assertions are
equivalent.

## Main results

* `CategoryTheory.ShortComplex.exists_cokernelIso_of_shortExact`: in an abelian category, the
  third term of a short exact sequence is the cokernel of its first map, compatibly with the
  cokernel projection. This is the converse of
  `CategoryTheory.ShortComplex.shortExact_of_cokernelIso`.
* `CategoryTheory.ShortComplex.exists_cokernelIso_iff_shortExact`: the two together, as an
  equivalence, for a monomorphism `f`.
* `AlgebraicGeometry.Scheme.Modules.exists_cokernelIso_iff_shortExact_of_mono` and
  `AlgebraicGeometry.Scheme.Modules.exists_cokernelIso_iff_shortExact_of_isRegularSection`: the
  equivalence for `𝒪_X ⟶ L ⟶ i_* i^* L` over the closed subscheme of an arbitrary
  quasi-coherent ideal sheaf, with monomorphy spelled categorically and as regularity of the
  section ([Stacks, Tag 01WY]) respectively.
* `AlgebraicGeometry.Scheme.Modules.cokernelIso_zeroScheme_iff_shortExact`: the two assertions of
  Tag 0C6K, at the zero scheme of the section, are equivalent.
* `AlgebraicGeometry.Scheme.Modules.shortExact_of_isRegularSection_zeroScheme`: the second
  assertion of Tag 0C6K, from the first taken as a hypothesis.

## Implementation notes

The general statements take the regularity of the section as the hypothesis
`Mono (L.unitHomEquiv.symm s)`: `AlgebraicGeometry.IsRegularSection` is by definition this
monomorphy ([Stacks, Tag 01WY]), so nothing is weakened by stating them categorically.

The vanishing of the composite `𝒪_X ⟶ L ⟶ i_* i^* L` is not a hypothesis anywhere here: it is part
of the conclusion of `CategoryTheory.ShortComplex.shortExact_of_cokernelIso`, since the
factorisation gives `f ≫ g = (f ≫ coker.π f) ≫ e.hom = 0`.

## References

* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 01WY](https://stacks.math.columbia.edu/tag/01WY)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe v u

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **The third term of a short exact sequence is the cokernel of its first map**, compatibly with
the cokernel projection. This is the converse of
`CategoryTheory.ShortComplex.shortExact_of_cokernelIso`. -/
theorem exists_cokernelIso_of_shortExact {A B D : C} {f : A ⟶ B} {g : B ⟶ D}
    (h : f ≫ g = 0) (hS : (ShortComplex.mk f g h).ShortExact) :
    ∃ e : cokernel f ≅ D, cokernel.π f ≫ e.hom = g := by
  refine ⟨IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel f) hS.gIsCokernel, ?_⟩
  exact IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel f) hS.gIsCokernel
    WalkingParallelPair.one

/-- **For a monomorphism `f`, realizing `D` as the cokernel of `f` through `g` is the same thing as
`0 ⟶ A ⟶ B ⟶ D ⟶ 0` being short exact.** -/
theorem exists_cokernelIso_iff_shortExact {A B D : C} (f : A ⟶ B) (hf : Mono f) (g : B ⟶ D) :
    (∃ e : cokernel f ≅ D, cokernel.π f ≫ e.hom = g) ↔
      ∃ h : f ≫ g = 0, (ShortComplex.mk f g h).ShortExact :=
  ⟨fun ⟨e, he⟩ => shortExact_of_cokernelIso f hf e he,
    fun ⟨h, hS⟩ => exists_cokernelIso_of_shortExact h hS⟩

end CategoryTheory.ShortComplex

namespace AlgebraicGeometry.Scheme.Modules

/-- **The two assertions of [Stacks, Tag 0C6K] are equivalent**, for the closed subscheme of an
arbitrary quasi-coherent ideal sheaf and an arbitrary sheaf of modules whose section is a
nonzerodivisor: the unit `g : L ⟶ i_* i^* L` realizes `i_* i^* L` as the cokernel of
multiplication by `s` if and only if `0 ⟶ 𝒪_X ⟶ L ⟶ i_* i^* L ⟶ 0` is short exact. -/
theorem exists_cokernelIso_iff_shortExact_of_mono (X : Scheme.{u}) (L : X.Modules)
    (I : X.IdealSheafData) (s : L.sections) (hs : Mono (L.unitHomEquiv.symm s)) :
    (∃ e : cokernel (L.unitHomEquiv.symm s) ≅
        (Scheme.Modules.pushforward I.subschemeι).obj
          ((Scheme.Modules.pullback I.subschemeι).obj L),
      cokernel.π (L.unitHomEquiv.symm s) ≫ e.hom =
        (Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app L) ↔
      (let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
       let f : O ⟶ L := L.unitHomEquiv.symm s
       let g : L ⟶ (Scheme.Modules.pushforward I.subschemeι).obj
           ((Scheme.Modules.pullback I.subschemeι).obj L) :=
         (Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app L
       ∃ h : f ≫ g = 0, (ShortComplex.mk f g h).ShortExact) :=
  ShortComplex.exists_cokernelIso_iff_shortExact _ hs _

/-- **The two assertions of [Stacks, Tag 0C6K] are equivalent**, with the hypothesis spelled as
regularity of the section in the sense of [Stacks, Tag 01WY]. This is the same statement as
`AlgebraicGeometry.Scheme.Modules.exists_cokernelIso_iff_shortExact_of_mono`:
`AlgebraicGeometry.IsRegularSection` is by definition that monomorphy. -/
theorem exists_cokernelIso_iff_shortExact_of_isRegularSection (X : Scheme.{u}) (L : X.Modules)
    (I : X.IdealSheafData) (s : L.sections)
    (hs : IsRegularSection X.sheaf.obj X.ringCatSheaf.property s) :
    (∃ e : cokernel (L.unitHomEquiv.symm s) ≅
        (Scheme.Modules.pushforward I.subschemeι).obj
          ((Scheme.Modules.pullback I.subschemeι).obj L),
      cokernel.π (L.unitHomEquiv.symm s) ≫ e.hom =
        (Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app L) ↔
      (let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
       let f : O ⟶ L := L.unitHomEquiv.symm s
       let g : L ⟶ (Scheme.Modules.pushforward I.subschemeι).obj
           ((Scheme.Modules.pullback I.subschemeι).obj L) :=
         (Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app L
       ∃ h : f ≫ g = 0, (ShortComplex.mk f g h).ShortExact) :=
  exists_cokernelIso_iff_shortExact_of_mono X L I s hs

/-- **The two assertions of [Stacks, Tag 0C6K], at the zero scheme of the section, are equivalent**
for an invertible module and a regular section. The zero scheme is `AlgebraicGeometry.zeroScheme`
([Stacks, Tag 02OQ]). -/
theorem cokernelIso_zeroScheme_iff_shortExact (X : Scheme.{u}) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : L.sections) (hs : IsRegularSection X.sheaf.obj X.ringCatSheaf.property s) :
    (let i := (zeroScheme X L (s.eval (op ⊤))).subschemeι
     ∃ e : cokernel (L.unitHomEquiv.symm s) ≅
         (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj L),
       cokernel.π (L.unitHomEquiv.symm s) ≫ e.hom =
         (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L) ↔
      (let i := (zeroScheme X L (s.eval (op ⊤))).subschemeι
       let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
       let f : O ⟶ L := L.unitHomEquiv.symm s
       let g : L ⟶ (Scheme.Modules.pushforward i).obj
           ((Scheme.Modules.pullback i).obj L) :=
         (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L
       ∃ h : f ≫ g = 0, (ShortComplex.mk f g h).ShortExact) :=
  exists_cokernelIso_iff_shortExact_of_isRegularSection X L
    (zeroScheme X L (s.eval (op ⊤))) s hs

/-- **[Stacks, Tag 0C6K], second assertion, from the first.** For an invertible module and a
regular section, the section followed by restriction to its zero scheme and pushforward is a short
exact sequence, as soon as the unit realizes `i_* i^* L` as the cokernel. -/
theorem shortExact_of_isRegularSection_zeroScheme (X : Scheme.{u}) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : L.sections) (hs : IsRegularSection X.sheaf.obj X.ringCatSheaf.property s)
    (hcok : let i := (zeroScheme X L (s.eval (op ⊤))).subschemeι
      ∃ e : cokernel (L.unitHomEquiv.symm s) ≅
          (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj L),
        cokernel.π (L.unitHomEquiv.symm s) ≫ e.hom =
          (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L) :
    let i := (zeroScheme X L (s.eval (op ⊤))).subschemeι
    let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
    let f : O ⟶ L := L.unitHomEquiv.symm s
    let g : L ⟶ (Scheme.Modules.pushforward i).obj
        ((Scheme.Modules.pullback i).obj L) :=
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L
    ∃ h : f ≫ g = 0, (ShortComplex.mk f g h).ShortExact :=
  (cokernelIso_zeroScheme_iff_shortExact X L s hs).1 hcok

end AlgebraicGeometry.Scheme.Modules

end
